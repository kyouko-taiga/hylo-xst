import DequeModule
import OrderedCollections
import Utilities

/// The type inference and checking algorithm of Hylo programs.
public struct Typer {

  /// The module being typed.
  public let module: Program.ModuleIdentity

  /// The program containing the module being typed.
  public internal(set) var program: Program

  /// A memoization cache for various internal operations.
  private var cache: Memos

  /// The set of declarations whose type is being computed.
  private var declarationsOnStack: Set<DeclarationIdentity>

  /// The identifier of the next fresh variable.
  private var nextFreshIdentifier: Int = 0

  /// A predicate to determine whether inference steps should be logged.
  private let isLoggingEnabled: ((AnySyntaxIdentity, Program) -> Bool)?

  /// The maximum depth of a derivation during implicit search.
  private let maxImplicitDepth = 100

  /// Creates an instance assigning types to syntax trees in `m`, which is a module in `p`.
  public init(
    typing m: Program.ModuleIdentity, in p: consuming Program,
    loggingInferenceWhere isLoggingEnabled: ((AnySyntaxIdentity, Program) -> Bool)? = nil
  ) {
    self.module = m
    self.program = p
    self.cache = .init(typing: module, in: program)
    self.declarationsOnStack = []
    self.isLoggingEnabled = isLoggingEnabled
  }

  /// Type checks the top-level declarations of `self.module`.
  public mutating func apply() {
    for d in program[module].topLevelDeclarations { check(d) }
  }

  /// Returns the resources held by this instance.
  public consuming func release() -> Program {
    self.program
  }

  // MARK: Caching

  /// A memoization cache for the operations of a `Typer`.
  private struct Memos {

    /// A table mapping identifiers to declarations.
    typealias LookupTable = OrderedDictionary<String, [DeclarationIdentity]>

    /// The cache of `Typer.lookup(_:atTopLevelOf:)`.
    var moduleToIdentifierToDeclaration: [LookupTable?]

    /// The cache of `Typer.imports(of:in:)`.
    var sourceToImports: [[Program.ModuleIdentity]?]

    /// The cache of `Typer.extensions(lexicallyIn:)`
    var scopeToExtensions: [ScopeIdentity: [ExtensionDeclaration.ID]]

    /// The cache of `Typer.declarations(lexicallyIn:)`.
    var scopeToLookupTable: [ScopeIdentity: LookupTable]

    /// The cache of `Typer.declarations(memberOf:visibleFrom:)`
    var scopeToTypeToLookupTable: [Scoped<AnyTypeIdentity>: LookupTable]

    /// The cache of `Typer.traits(visibleFrom:)`
    var scopeToTraits: [ScopeIdentity: [TraitDeclaration.ID]]

    /// The cache of `Typer.summon(_:in:)`.
    var scopeToSummoned: [ScopeIdentity: [AnyTypeIdentity: [SummonResult]]]

    /// The cache of `Typer.typeOfSelf(in:)`.
    var scopeToTypeOfSelf: [ScopeIdentity: AnyTypeIdentity?]

    /// Creates an instance for typing `m`, which is a module in `p`.
    init(typing m: Program.ModuleIdentity, in p: Program) {
      self.moduleToIdentifierToDeclaration = .init(repeating: nil, count: p.modules.count)
      self.sourceToImports = .init(repeating: nil, count: p[m].sources.count)
      self.scopeToExtensions = [:]
      self.scopeToLookupTable = [:]
      self.scopeToTypeToLookupTable = [:]
      self.scopeToTraits = [:]
      self.scopeToSummoned = [:]
      self.scopeToTypeOfSelf = [:]
    }

  }

  // MARK: Type relations

  /// Returns `t` without any type alias.
  public mutating func dealiased(_ t: AnyTypeIdentity) -> AnyTypeIdentity {
    program.types.map(t) { (s, u) in
      if let a = s[u] as? TypeAlias {
        return .stepInto(a.aliasee)
      } else if u[.hasAliases] {
        return .stepInto(u)
      } else {
        return .stepOver(u)
      }
    }
  }

  /// Returns `true` iff `t` and `u` are equal.
  public func equal(_ t: AnyTypeIdentity, _ u: AnyTypeIdentity) -> Bool {
    (t == u)
  }

  // MARK: Type checking

  /// Type checks `d`.
  private mutating func check(_ d: DeclarationIdentity) {
    switch program.kind(of: d) {
    case AssociatedTypeDeclaration.self:
      check(castUnchecked(d, to: AssociatedTypeDeclaration.self))
    case BindingDeclaration.self:
      check(castUnchecked(d, to: BindingDeclaration.self))
    case ConformanceDeclaration.self:
      check(castUnchecked(d, to: ConformanceDeclaration.self))
    case ExtensionDeclaration.self:
      check(castUnchecked(d, to: ExtensionDeclaration.self))
    case FunctionDeclaration.self:
      check(castUnchecked(d, to: FunctionDeclaration.self))
    case GenericParameterDeclaration.self:
      check(castUnchecked(d, to: GenericParameterDeclaration.self))
    case InitializerDeclaration.self:
      check(castUnchecked(d, to: InitializerDeclaration.self))
    case ParameterDeclaration.self:
      check(castUnchecked(d, to: ParameterDeclaration.self))
    case StructDeclaration.self:
      check(castUnchecked(d, to: StructDeclaration.self))
    case TraitDeclaration.self:
      check(castUnchecked(d, to: TraitDeclaration.self))
    case TypeAliasDeclaration.self:
      check(castUnchecked(d, to: TypeAliasDeclaration.self))
    default:
      program.unexpected(d)
    }
  }

  /// Type checks `d`.
  private mutating func check(_ d: AssociatedTypeDeclaration.ID) {
    _ = declaredType(of: d)
    // TODO
  }

  /// Type checks `d`.
  private mutating func check(_ d: BindingDeclaration.ID) {
    let t = declaredType(of: d)
    if let i = program[d].initializer {
      check(i, expecting: t)
    }

    let p = program.parent(containing: d)
    program.forEachVariable(introducedBy: d) { (v, _) in
      if v.erased != lookup(program[v].identifier.value, lexicallyIn: p).uniqueElement?.erased {
        report(program.duplicateDeclaration(at: program[v].site))
      }
    }
  }

  /// Type checks `d`.
  private mutating func check(_ d: ConformanceDeclaration.ID) {
    _ = declaredType(of: d)

    check(program[d].contextParameters)
    for m in program[d].members { check(m) }

    // TODO: Check requirement satisfaction
  }

  /// Type checks `d`.
  private mutating func check(_ d: ExtensionDeclaration.ID) {
    _ = extendeeType(d)
    for m in program[d].members { check(m) }
  }

  /// Type checks `d`.
  private mutating func check(_ d: FunctionDeclaration.ID) {
    let t = declaredType(of: d)

    // Nothing more to do if the declaration doesn't have an arrow type.
    if let a = program.types[program.types.head(t)] as? Arrow {
      check(program[d].contextParameters)
      check(program[d].parameters)
      check(body: program[d].body, of: .init(d), expectingOutputType: a.output)
    }
  }

  /// Type checks `d`.
  private mutating func check(_ d: GenericParameterDeclaration.ID) {
    _ = declaredType(of: d)
  }

  /// Type checks `d`.
  private mutating func check(_ d: InitializerDeclaration.ID) {
    let t = declaredType(of: d)

    // Nothing more to do if the declaration doesn't have an arrow type.
    if let a = program.types[program.types.head(t)] as? Arrow {
      check(program[d].parameters)
      check(body: program[d].body, of: .init(d), expectingOutputType: a.output)
    }
  }

  /// Type checks `body` as the definition of `d`, which declares a function or susbscript that
  /// outputs an instance of `r`.
  private mutating func check(
    body: [StatementIdentity]?, of d: DeclarationIdentity,
    expectingOutputType r: AnyTypeIdentity
  ) {
    if let b = body {
      // Is the function expression-bodied?
      if let e = b.uniqueElement.flatMap(program.castToExpression(_:)) {
        check(e, expecting: r)
      } else {
        for s in b { check(s) }
      }
    } else if requiresDefinition(d) {
      // Only requirements, FFIs, and external functions can be without a body.
      let s = program.spanForDiagnostic(about: d)
      report(.init(.error, "declaration requires a body", at: s))
    }
  }

  /// Type checks `d`.
  private mutating func check(_ d: ParameterDeclaration.ID) {
    let ascription = declaredType(of: d)

    // Bail out if the ascription has an error.
    guard let a = program.types[ascription] as? RemoteType else {
      assert(ascription[.hasError])
      return
    }

    if let v = program[d].default {
      check(v, expecting: a.projectee)
    }
  }

  /// Type checks `d`.
  private mutating func check(_ d: StructDeclaration.ID) {
    _ = declaredType(of: d)
    for m in program[d].members { check(m) }
  }

  /// Type checks `d`.
  private mutating func check(_ d: TraitDeclaration.ID) {
    _ = declaredType(of: d)
    // TODO
  }

  /// Type checks `d`.
  private mutating func check(_ d: TypeAliasDeclaration.ID) {
    _ = declaredType(of: d)
    // TODO
  }

  /// Type checks `ps`.
  private mutating func check(_ ps: [ParameterDeclaration.ID]) {
    var siblings: [String: ParameterDeclaration.ID] = .init(minimumCapacity: ps.count)
    for p in ps {
      check(p)

      // Check for duplicate parameters.
      modify(&siblings[program[p].identifier.value]) { (q) in
        if let previous = q {
          let m = program.duplicateDeclaration(
            at: program.spanForDiagnostic(about: p),
            previousDeclarations: [program.spanForDiagnostic(about: previous)])
          report(m)
        } else {
          q = p
        }
      }
    }
  }

  /// Type checks `ps`.
  private mutating func check(_ ps: StaticParameters) {
    for p in ps.explicit { check(p) }
    for p in ps.implicit { check(p) }
  }

  /// Returns `true` iff `d` needs a user-defined a definition.
  ///
  /// A declaration requires a definition unless it is a trait requirement, an FFI, an external
  /// function, or a memberwise initializer.
  private func requiresDefinition(_ d: DeclarationIdentity) -> Bool {
    switch program.kind(of: d) {
    case FunctionDeclaration.self:
      let f = program.castUnchecked(d, to: FunctionDeclaration.self)
      return !program.isRequirement(f) && !program.isFFI(f) && !program.isExternal(f)

    case InitializerDeclaration.self:
      let f = program.castUnchecked(d, to: InitializerDeclaration.self)
      return !program[f].isMemberwise

    default:
      return !program.isRequirement(d)
    }
  }

  /// Type checks `e` and returns its type, which is expected to be `r` from the context of `e`.
  @discardableResult
  private mutating func check(
    _ e: ExpressionIdentity, inContextExpecting r: AnyTypeIdentity? = nil
  ) -> AnyTypeIdentity {
    var c = InferenceContext(expectedType: r)
    let t = inferredType(of: e, in: &c)
    let s = discharge(c.obligations, relatedTo: e)
    return program.types.reify(t, applying: s.substitutions)
  }

  /// Type checks `e` expecting it to have type `r` and reporting an error if it doesn't.
  private mutating func check(_ e: ExpressionIdentity, expecting r: AnyTypeIdentity) {
    let u = check(e, inContextExpecting: r)
    if (u != r) && !equal(u, .never) && !u[.hasError] {
      let m = program.format("expected '%T', found '%T'", [r, u])
      report(.init(.error, m, at: program[e].site))
    }
  }

  /// Type checks `e`, which occurs as a statement.
  private mutating func checkAsStatement(_ e: ExpressionIdentity) {
    let u = check(e, inContextExpecting: .void)
    if !equal(u, .void) && !u[.hasError] {
      let m = program.format("unused value of type %T", [u])
      report(.init(.error, m, at: program[e].site))
    }
  }

  /// Type checks `s`.
  private mutating func check(_ s: StatementIdentity) {
    switch program.kind(of: s) {
    case Discard.self:
      check(program.castUnchecked(s, to: Discard.self))
    case Return.self:
      check(program.castUnchecked(s, to: Return.self))
    case _ where program.isExpression(s):
      checkAsStatement(ExpressionIdentity(uncheckedFrom: s.erased))
    case _ where program.isDeclaration(s):
      check(DeclarationIdentity(uncheckedFrom: s.erased))
    default:
      program.unexpected(s)
    }
  }

  /// Type checks `s`.
  private mutating func check(_ s: Discard.ID) {
    check(program[s].value)
    program[module].setType(.void, for: s)
  }

  /// Type checks `s`.
  private mutating func check(_ s: Return.ID) {
    let u = expectedOutputType(in: program.parent(containing: s)) ?? .error

    if let v = program[s].value {
      if u != .error {
        check(v, expecting: u)
      } else {
        check(v)
      }
    } else if !equal(u, .void) {
      let m = program.format("expected value of type '%T'", [u])
      let s = program.spanForDiagnostic(about: s)
      report(.init(.error, m, at: s))
    }

    program[module].setType(.void, for: s)
  }

  /// Returns the declared type of `d` without type checking its contents.
  private mutating func declaredType(of d: DeclarationIdentity) -> AnyTypeIdentity {
    switch program.kind(of: d) {
    case AssociatedTypeDeclaration.self:
      return declaredType(of: castUnchecked(d, to: AssociatedTypeDeclaration.self))
    case BindingDeclaration.self:
      return declaredType(of: castUnchecked(d, to: BindingDeclaration.self))
    case ConformanceDeclaration.self:
      return declaredType(of: castUnchecked(d, to: ConformanceDeclaration.self))
    case FunctionDeclaration.self:
      return declaredType(of: castUnchecked(d, to: FunctionDeclaration.self))
    case GenericParameterDeclaration.self:
      return declaredType(of: castUnchecked(d, to: GenericParameterDeclaration.self))
    case InitializerDeclaration.self:
      return declaredType(of: castUnchecked(d, to: InitializerDeclaration.self))
    case ParameterDeclaration.self:
      return declaredType(of: castUnchecked(d, to: ParameterDeclaration.self))
    case StructDeclaration.self:
      return declaredType(of: castUnchecked(d, to: StructDeclaration.self))
    case TraitDeclaration.self:
      return declaredType(of: castUnchecked(d, to: TraitDeclaration.self))
    case TypeAliasDeclaration.self:
      return declaredType(of: castUnchecked(d, to: TypeAliasDeclaration.self))
    case VariableDeclaration.self:
      return declaredType(of: castUnchecked(d, to: VariableDeclaration.self))
    default:
      program.unexpected(d)
    }
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: AssociatedTypeDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[module].type(assignedTo: d) { return memoized }

    let t = typeOfSelf(in: program.parent(containing: d))!
    let u = metatype(of: AssociatedType(declaration: d, qualification: t)).erased
    program[module].setType(u, for: d)
    return t
  }

  /// Returns the declared type of `d`, using inference if necessary.
  private mutating func declaredType(of d: BindingDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[module].type(assignedTo: d) { return memoized }

    // Is it the first time we enter this method for `d`?
    if declarationsOnStack.insert(.init(d)).inserted {
      defer { declarationsOnStack.remove(.init(d)) }

      var c = InferenceContext()
      let p = inferredType(of: d, in: &c)
      let s = discharge(c.obligations, relatedTo: d)
      let u = program.types.reify(p, applying: s.substitutions)

      ascribe(u, to: program[d].pattern)
      program[module].setType(u, for: d)
      return u
    }

    // Cyclic reference detected.
    else {
      let s = program[program[program[d].pattern].pattern].site
      report(.init(.error, "declaration refers to itself", at: s))
      return .error
    }
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: ConformanceDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[module].type(assignedTo: d) { return memoized }

    var result = declaredConformanceType(program[d].extendee, program[d].concept)

    let cs = program[d].contextParameters.implicit.map({ (p) in declaredType(of: p) })
    if !cs.isEmpty {
      result = demand(Implication(context: cs, head: result)).erased
    }

    let ps = program[d].contextParameters.explicit.compactMap { (p) in
      let t = declaredType(of: p)
      return program.types
        .select(\Metatype.inhabitant, on: t)
        .flatMap({ (m) in program.types.cast(m, to: TypeParameter.self) })
    }
    if !ps.isEmpty {
      result = demand(UniversalType(parameters: ps, body: result)).erased
    }

    program[module].setType(result, for: d)
    return result
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: FunctionDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[module].type(assignedTo: d) { return memoized }

    let inputs = declaredTypes(of: program[d].parameters)
    let output = program[d].output.map { (a) in
      evaluateTypeAscription(a)
    }

    let environment: AnyTypeIdentity
    if program.isMember(d) {
      let r = typeOfSelf(in: program.parent(containing: d))!
      let e = demand(RemoteType(projectee: r, access: program[d].effect.value)).erased
      environment = demand(Tuple(elements: [.init(label: "self", type: e)])).erased
    } else {
      environment = .void
    }

    let a = Arrow(
      environment: environment,
      inputs: inputs,
      output: output ?? .void)
    let head = demand(a).erased

    let context = program[d].contextParameters.implicit.map { (p) in
      declaredType(of: p)
    }

    if context.isEmpty {
      program[module].setType(head, for: d)
      return head
    } else {
      let u = demand(Implication(context: context, head: head)).erased
      program[module].setType(u, for: d)
      return u
    }
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: GenericParameterDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[module].type(assignedTo: d) { return memoized }

    let t = metatype(of: TypeParameter(declaration: d)).erased
    program[module].setType(t, for: d)
    return t
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: InitializerDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[module].type(assignedTo: d) { return memoized }

    // Could we resolve the type of "Self"?
    let output = typeOfSelf(in: program.parent(containing: d))!
    if output == .error { return .error }

    // Are we looking at a memberwise initializer?
    else if program[d].isMemberwise {
      // Memberwise initializers can only appear nested in a struct declaration.
      let s = program.parent(containing: d, as: StructDeclaration.self)!

      var inputs: [Parameter] = []
      for m in program[s].members {
        guard let b = program.cast(m, to: BindingDeclaration.self) else { continue }

        // Make sure there's a type for each of the variables introduced by the declaration.
        _ = declaredType(of: b)
        program.forEachVariable(introducedBy: b) { (v, _) in
          let t = program[module].type(assignedTo: b) ?? .error
          let u = demand(RemoteType(projectee: t, access: .sink)).erased
          inputs.append(
            Parameter(
              declaration: nil,
              label: program[v].identifier.value, type: u,
              isImplicit: false))
        }
      }

      let t = demand(Arrow(inputs: inputs, output: output)).erased
      program[module].setType(t, for: d)
      return t
    }

    // We're looking at a custom initializer.
    else {
      let inputs = declaredTypes(of: program[d].parameters)
      let t = demand(Arrow(inputs: inputs, output: output)).erased
      program[module].setType(t, for: d)
      return t
    }
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: ParameterDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[module].type(assignedTo: d) { return memoized }

    let t = program[d].ascription.map({ (a) in evaluateTypeAscription(.init(a)) }) ?? {
      report(.init(.error, "parameter requires ascription", at: program[d].site))
      return .error
    }()

    program[module].setType(t, for: d)
    return t
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: StructDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[module].type(assignedTo: d) { return memoized }

    let t = metatype(of: Struct(declaration: d)).erased
    program[module].setType(t, for: d)
    return t
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: TraitDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[module].type(assignedTo: d) { return memoized }

    let t = metatype(of: Trait(declaration: d)).erased
    program[module].setType(t, for: d)
    return t
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: TypeAliasDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[module].type(assignedTo: d) { return memoized }

    // Is it the first time we enter this method for `d`?
    if declarationsOnStack.insert(.init(d)).inserted {
      defer { declarationsOnStack.remove(.init(d)) }

      switch evaluateTypeAscription(program[d].aliasee) {
      case .error:
        program[module].setType(.error, for: d)
        return .error
      case let aliasee:
        let t = metatype(of: TypeAlias(declaration: d, aliasee: aliasee)).erased
        program[module].setType(t, for: d)
        return t
      }
    }

    // Cyclic reference detected.
    else {
      let n = program[d].identifier
      report(.init(.error, "definition of '\(n)' refers to itself", at: n.site))
      return .error
    }
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: VariableDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[module].type(assignedTo: d) { return memoized }

    // Variable declarations outside of a binding declaration are typed through their containing
    // pattern, which is visited before any reference to the variable can be formed.
    let b = program.bindingDeclaration(containing: d) ?? unreachable("pattern is not typed")
    _ = declaredType(of: b)
    return program[module].type(assignedTo: d) ?? .error
  }

  /// Returns the declared properties of the parameters in `ds` without checking.
  private mutating func declaredTypes(of ps: [ParameterDeclaration.ID]) -> [Parameter] {
    var result: [Parameter] = []
    for p in ps {
      result.append(
        Parameter(
          declaration: p,
          label: program[p].label?.value,
          type: declaredType(of: p),
          isImplicit: false))
    }
    return result
  }

  /// Returns the type of a value witnessing the conformance of `extendee` to `concept`.
  private mutating func declaredConformanceType(
    _ extendee: ExpressionIdentity, _ concept: ExpressionIdentity
  ) -> AnyTypeIdentity {
    let e = evaluateTypeAscription(extendee)
    let c = evaluateTypeAscription(concept)

    // Was there an error?
    if (e == .error) || (c == .error) {
      return .error
    }

    // Is the expression of the concept denoting something other than a trait?
    else if !(program.types[c] is Trait) {
      let m = program.format("'%T' is not a trait", [c])
      let s = program[concept].site
      report(.init(.error, m, at: s))
      return .error
    }

    // All is well.
    else {
      return demand(TypeApplication(abstraction: c, arguments: [.type(e)])).erased
    }
  }

  /// Returns the type that `d` extends.
  private mutating func extendeeType(_ d: ExtensionDeclaration.ID) -> AnyTypeIdentity {
    if let t = program[d.module].type(assignedTo: d) {
      return t
    } else {
      assert(d.module == module, "dependency is not typed")
      let t = ignoring(d, { (me) in me.evaluateTypeAscription(me.program[d].extendee) })
      program[module].setType(t, for: d)
      return t
    }
  }

  /// Ascribes `t` to `p` and its children, reporting an error if `t` doesn't match `p`'s shape.
  private mutating func ascribe(_ t: AnyTypeIdentity, to p: PatternIdentity) {
    switch program.kind(of: p) {
    case BindingPattern.self:
      ascribe(t, to: program.castUnchecked(p, to: BindingPattern.self))
    case TuplePattern.self:
      ascribe(t, to: program.castUnchecked(p, to: TuplePattern.self))
    case VariableDeclaration.self:
      ascribe(t, to: program.castUnchecked(p, to: VariableDeclaration.self))
    default:
      check(program.castToExpression(p)!, expecting: t)
    }
  }

  /// Ascribes `t` to `p` and its children, reporting an error if `t` doesn't match `p`'s shape.
  private mutating func ascribe(_ t: AnyTypeIdentity, to p: BindingPattern.ID) {
    program[module].setType(t, for: p)
    ascribe(t, to: program[p].pattern)
  }

  /// Ascribes `t` to `p` and its children, reporting an error if `t` doesn't match `p`'s shape.
  private mutating func ascribe(_ t: AnyTypeIdentity, to p: TuplePattern.ID) {
    guard let u = program.types[t] as? Tuple else {
      let m = program.format("tuple pattern cannot match values of type '%T'", [t])
      report(.init(.error, m, at: program[p].site))
      program[module].setType(.error, for: p)
      return
    }

    guard u.labelsEqual(program[p].elements, \.label?.value) else {
      let d: Diagnostic = program.incompatibleLabels(
        found: program[p].elements.map(\.label?.value), expected: u.labels,
        at: program[p].site)
      report(d)
      program[module].setType(.error, for: p)
      return
    }

    program[module].setType(t, for: p)
    for i in 0 ..< u.elements.count {
      ascribe(u.elements[i].type, to: program[p].elements[i].value)
    }
  }

  /// Ascribes `t` to `p` and its children, reporting an error if `t` doesn't match `p`'s shape.
  private mutating func ascribe(_ t: AnyTypeIdentity, to p: VariableDeclaration.ID) {
    program[module].setType(t, for: p)
  }

  // MARK: Type inference

  /// The grammatical role of a syntax tree plays in an expression.
  private enum SyntaxRole {

    /// The expression is used in an unspecified way.
    case unspecified

    /// The expression denotes as the callee of a function call.
    case function(labels: [String?])

    /// The expression denotes as the callee of a subscript call.
    case `subscript`(labels: [String?])

    /// Creates the role of a callee applied with given `style` and `labels`.
    init(_ style: Call.Style, labels: [String?]) {
      switch style {
      case .parenthesized:
        self = .function(labels: labels)
      case .bracketed:
        self = .subscript(labels: labels)
      }
    }

  }

  /// The context in which the type of a syntax tree is being inferred.
  private struct InferenceContext {

    /// The way in which the tree is used.
    let role: SyntaxRole

    /// The type expected to be inferred given the context.
    let expectedType: AnyTypeIdentity?

    /// A set of formulae about the type being inferred.
    var obligations: Obligations

    /// Creates a context with the given properties.
    init(expectedType: AnyTypeIdentity? = nil, role: SyntaxRole = .unspecified) {
      self.expectedType = expectedType
      self.role = role
      self.obligations = .init()
    }

    /// Calls `action` with an inference context having the given properties and extending the
    /// obligations of `self`.
    mutating func withSubcontext<T>(
      expectedType: AnyTypeIdentity? = nil, role: SyntaxRole = .unspecified,
      do action: (inout Self) -> T
    ) -> T {
      var s = InferenceContext(expectedType: expectedType, role: role)
      swap(&self.obligations, &s.obligations)
      defer { swap(&self.obligations, &s.obligations) }
      return action(&s)
    }

  }

  /// Returns the inferred type of `e`, which occurs in `context`.
  private mutating func inferredType(
    of e: ExpressionIdentity, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    switch program.kind(of: e) {
    case BooleanLiteral.self:
      return inferredType(of: castUnchecked(e, to: BooleanLiteral.self), in: &context)
    case Call.self:
      return inferredType(of: castUnchecked(e, to: Call.self), in: &context)
    case NameExpression.self:
      return inferredType(of: castUnchecked(e, to: NameExpression.self), in: &context)
    case RemoteTypeExpression.self:
      return inferredType(of: castUnchecked(e, to: RemoteTypeExpression.self), in: &context)
    case TupleLiteral.self:
      return inferredType(of: castUnchecked(e, to: TupleLiteral.self), in: &context)
    case TupleTypeExpression.self:
      return inferredType(of: castUnchecked(e, to: TupleTypeExpression.self), in: &context)
    default:
      program.unexpected(e)
    }
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: BooleanLiteral.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    fatalError("TODO")
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: Call.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let f = inferredType(calleeOf: e, in: &context)

    // Bail out if the callee has an error type.
    if f == .error {
      return context.obligations.assume(e, hasType: .error, at: program[e].site)
    } else {
      var i: [CallConstraint.Argument] = []
      for a in program[e].arguments {
        let t = context.withSubcontext { (ctx) in inferredType(of: a.value, in: &ctx) }
        i.append(.init(label: a.label?.value, type: t))
      }

      let m = program.isMarkedMutating(program[e].callee)
      let o = (program.types[f] as? any Callable)?.output(calleeIsMutating: m)
        ?? context.expectedType
        ?? fresh().erased
      let k = CallConstraint(
        callee: f, arguments: i, output: o, origin: e, site: program[e].site)

      context.obligations.assume(k)
      return context.obligations.assume(e, hasType: o, at: program[e].site)
    }
  }

  /// Returns the inferred type of `e`'s callee.
  private mutating func inferredType(
    calleeOf e: Call.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let r = SyntaxRole(program[e].style, labels: program[e].labels)
    let f = context.withSubcontext(role: r) { (ctx) in
      inferredType(of: program[e].callee, in: &ctx)
    }

    // Is the callee bound to a type?
    if program.types[f] is Metatype {
      let c = program[e].callee
      let n = program[module].insert(
        NameExpression(
          qualification: .explicit(c),
          name: .init(.init(identifier: "new"), at: program[c].site),
          site: program[c].site),
        in: program.parent(containing: e))
      program[module].replace(.init(e), for: program[e].replacing(callee: .init(n)))
      return inferredType(calleeOf: e, in: &context)
    }

    // Otherwise, returns the inferred type as-is.
    else { return f }
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: NameExpression.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    resolve(e, in: &context)
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: RemoteTypeExpression.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let t = evaluateTypeAscription(program[e].projectee)
    let u = metatype(of: RemoteType(projectee: t, access: program[e].access.value)).erased
    return context.obligations.assume(e, hasType: u, at: program[e].site)
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: TupleLiteral.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    /// Returns the inferred type of `e`, possibly expected to have type `h`.
    func type(of e: LabeledExpression, expecting h: AnyTypeIdentity?) -> Tuple.Element {
      let u = context.withSubcontext { (ctx) in inferredType(of: e.value, in: &ctx) }
      return .init(label: e.label?.value, type: u)
    }

    let es = program[e].elements
    var ts: [Tuple.Element] = []

    // If the expected type is a tuple compatible with the shape of the expression, propagate that
    // information down the expression tree.
    if
      let h = context.expectedType.flatMap({ (t) in program.types[t] as? Tuple }),
      h.labelsEqual(es, \.label?.value)
    {
      for (e, t) in zip(es, h.elements) { ts.append(type(of: e, expecting: t.type)) }
    }

    // Otherwise, infer the type of the expression from the leaves and use type constraints to
    // detect potential mismatch.
    else {
      for e in es { ts.append(type(of: e, expecting: nil)) }
    }

    let r = demand(Tuple(elements: ts)).erased
    return context.obligations.assume(e, hasType: r, at: program[e].site)
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: TupleTypeExpression.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let es = program[e].elements.map { (e) in
      Tuple.Element(label: e.label?.value, type: evaluateTypeAscription(e.value))
    }

    let t = metatype(of: Tuple(elements: es)).erased
    return context.obligations.assume(e, hasType: t, at: program[e].site)
  }

  /// Returns the inferred type of `p`, which occurs in `context`.
  private mutating func inferredType(
    of p: PatternIdentity, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    switch program.kind(of: p) {
    case BindingPattern.self:
      unreachable()
    case VariableDeclaration.self:
      return inferredType(of: castUnchecked(p, to: VariableDeclaration.self), in: &context)

    default:
      // Other patterns are expressions.
      let e = program.castToExpression(p) ?? unreachable()
      return inferredType(of: e, in: &context)
    }
  }

  /// Returns the inferred type of `d`, which occurs in `context`.
  private mutating func inferredType(
    of d: BindingDeclaration.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    // Fast path: if the pattern has no ascription, the type type is inferred from the initializer.
    guard let a = program[program[d].pattern].ascription else {
      let i = program[d].initializer ?? unreachable("ill-formed binding declaration")
      let t = inferredType(of: i, in: &context)
      return context.obligations.assume(d, hasType: t, at: program[d].site)
    }

    // Slow path: infer a type from the ascription and the initializer (if any).
    var c = InferenceContext()
    let p = evaluateTypeAscription(a)

    if let i = program[d].initializer {
      let v = c.withSubcontext(expectedType: p, do: { (s) in inferredType(of: i, in: &s) })
      if v != .error {
        c.obligations.assume(TypeEquality(lhs: p, rhs: v, site: program[i].site))
      }
    }

    return context.obligations.assume(d, hasType: p, at: program[d].site)
  }

  /// Returns the inferred type of `d`, which occurs in `context`.
  private mutating func inferredType(
    of d: VariableDeclaration.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let t = fresh().erased
    return context.obligations.assume(d, hasType: t, at: program[d].site)
  }

  /// Constrains the name component in `r` to be a reference to one of `r`'s resolution candidates
  /// in `o`, and returns the inferred type of `r`.
  private mutating func assume(
    _ n: NameExpression.ID, boundTo cs: [NameResolutionCandidate], in o: inout Obligations
  ) -> AnyTypeIdentity {
    // If there's only one candidate, we're done.
    if let pick = cs.uniqueElement {
      // TODO: Instantiate

      o.assume(n, boundTo: pick.reference)
      return o.assume(n, hasType: pick.type, at: program[n].site)
    }

    // Otherwise, create an overload set.
    else {
      assert(!cs.isEmpty)
      let t = fresh().erased
      o.assume(OverloadConstraint(name: n, type: t, candidates: cs, site: program[n].site))
      return o.assume(n, hasType: t, at: program[n].site)
    }
  }

  /// Proves the obligations `o`, which relate to the well-typedness of `n`, returning the best
  /// assignment of universally quantified variables.
  @discardableResult
  private mutating func discharge<T: SyntaxIdentity>(
    _ o: Obligations, relatedTo n: T
  ) -> Solution {
    if o.constraints.isEmpty {
      let s = Solution(bindings: o.bindings)
      commit(s, to: o)
      return s
    } else {
      var solver = Solver(o, withLoggingEnabled: isLoggingEnabled?(n.erased, program) ?? false)
      let s = solver.solution(using: &self)
      commit(s, to: o)
      return s
    }
  }

  private mutating func commit(_ s: Solution, to o: Obligations) {
    report(s.diagnostics.elements)
    for (n, t) in o.syntaxToType {
      program[module].setType(t, for: n)
    }
    for (n, r) in s.bindings {
      program[module].bind(n, to: r)
    }
    for (n, e) in s.elaborations {
      let arguments = e.elements.map({ (b) in elaborate(b, in: n) })
      program[module].replace(.init(n), for: program[n].replacing(arguments: arguments))
    }
  }

  /// Returns the elaboration of `b` which describes an argument in `n`.
  private mutating func elaborate(_ b: ParameterBinding, in n: Call.ID) -> LabeledExpression {
    switch b {
    case .explicit(let i):
      return program[n].arguments[i]

    case .implicit:
      fatalError("TODO")

    case .defaulted(let d):
      let t = program[module].type(assignedTo: program[d].default!) ?? .error
      let n = program[module].insert(
        SynthethicExpression(value: .defaultArgument(d), site: program[n].site),
        in: program.parent(containing: n))
      program[module].setType(t, for: n)
      return .init(label: program[d].label, value: .init(n))
    }
  }

  /// Returns the type of a name expression bound to `d`.
  private mutating func typeOfName(boundTo d: DeclarationIdentity) -> AnyTypeIdentity {
    let t = declaredType(of: d)
    return (program.types[t] as? RemoteType)?.projectee ?? t
  }

  /// Returns the value of `Self` evaluated in `s`, or `nil` if `s` isn't notionally in the scope
  /// of a type declaration.
  private mutating func typeOfSelf(in s: ScopeIdentity) -> AnyTypeIdentity? {
    if let memoized = cache.scopeToTypeOfSelf[s] { return memoized }

    guard let n = s.node else { return nil }
    let result: AnyTypeIdentity?

    switch program.kind(of: n) {
    case ConformanceDeclaration.self:
      fatalError()
    case ExtensionDeclaration.self:
      result = extendeeType(program.castUnchecked(n, to: ExtensionDeclaration.self))
    case StructDeclaration.self:
      result = typeOfSelf(in: program.castUnchecked(n, to: StructDeclaration.self))
    case TraitDeclaration.self:
      result = typeOfSelf(in: program.castUnchecked(n, to: TraitDeclaration.self))
    default:
      result = typeOfSelf(in: program.parent(containing: n))
    }

    cache.scopeToTypeOfSelf[s] = .some(result)
    return result
  }

  /// Returns the value of `Self` evaluated in the lexical scope of `d`.
  private mutating func typeOfSelf(in d: StructDeclaration.ID) -> AnyTypeIdentity {
    let t = declaredType(of: .init(d))
    return (program.types[t] as? Metatype)?.inhabitant ?? .error
  }

  /// Returns the value of `Self` evaluated in the lexical scope of `d`.
  private mutating func typeOfSelf(in d: TraitDeclaration.ID) -> AnyTypeIdentity {
    declaredType(of: program[d].conformer)
  }

  /// Returns the type of the implementation satisfying `requirement` in `model`.
  ///
  /// - Parameters:
  ///   - requirement: The declaration of a concept requirement.
  ///   - witness: The witness of a type's conformance to the concept defining `requirement`.
  private mutating func typeOfImplementation(
    satisfying requirement: DeclarationIdentity, in witness: Model
  ) -> AnyTypeIdentity {
    switch witness {
    case .concrete(_, let implementations):
      return implementations[requirement]!.type

    case .abstract(_):
      let (concept, conformer) = program.types.castToTraitApplication(witness.type)!
      let s = typeOfSelf(in: program.types[concept].declaration)
      let t = declaredType(of: requirement)
      return program.types.substitute(s, for: conformer, in: t)
    }
  }

  // MARK: Compile-time evaluation

  /// Returns the value of `e` evaluated as a type ascription.
  private mutating func evaluateTypeAscription(_ e: ExpressionIdentity) -> AnyTypeIdentity {
    var c = InferenceContext()
    let t = inferredType(of: e, in: &c)
    let s = discharge(c.obligations, relatedTo: e)
    let u = program.types.reify(t, applying: s.substitutions)

    if let m = program.types[u] as? Metatype {
      return m.inhabitant
    } else if u == .error {
      // Error already reported.
      return .error
    } else {
      report(.init(.error, "expression does not denote a type", at: program[e].site))
      return .error
    }
  }

  /// Returns the value of `w`.
  private mutating func evaluate(_ w: WitnessExpression) -> Value {
    switch w.value {
    case .reference(let r):
      return evaluate(r)
    case .termApplication(let f, _):
      return evaluate(f)
    case .typeApplication(let f, _):
      return evaluate(f)
    }
  }

  /// Returns the value of the entity referred to by `r`.
  private mutating func evaluate(_ r: DeclarationReference) -> Value {
    precondition(isStable(r), "declaration reference is not stable")

    switch r {
    case .direct(let d) where program.kind(of: d) == ConformanceDeclaration.self:
      return evaluate(program.castUnchecked(d, to: ConformanceDeclaration.self))
    default:
      fatalError("TODO")
    }
  }

  /// Returns the value of `d`, which witnesses some conformance.
  ///
  /// The returned value is a model witnessing the conformance declared by `d`, or an error term if
  /// `d` is ill-formed.
  private mutating func evaluate(_ d: ConformanceDeclaration.ID) -> Value {
    let t = declaredType(of: d)
    let witness = program.types.head(t)
    guard let (concept, _) = program.types.castToTraitApplication(witness) else {
      assert(t == .error)
      return .term(.error)
    }

    // Trivial if the declaration is abstract.
    if program[d].isAbstract {
      return .init(Model.abstract(type: program.types.castUnchecked(t)))
    }

    /// The members of the concept.
    let ms = program[program.types[concept].declaration].members

    /// A table from concept requirement to its implementation.
    var ns: OrderedDictionary<DeclarationIdentity, Model.Implementation> = [:]

    // Find the implementation of associated types.
    for a in program.collect(AssociatedTypeDeclaration.self, in: ms) {
      guard let i = implementation(of: a, in: d) else {
        reportMissingImplementation(of: a)
        return .term(.error)
      }

      let u = declaredType(of: i)
      if program.types.kind(of: u) == Metatype.self {
        ns[DeclarationIdentity(a)] = .explicit(.direct(i), u)
      } else {
        reportMissingImplementation(of: a)
        return .term(.error)
      }
    }

    // TODO: method requirements

    return .init(Model(program.types.castUnchecked(t), implementations: ns))
  }

  private mutating func implementation(
    of a: AssociatedTypeDeclaration.ID, in d: ConformanceDeclaration.ID
  ) -> DeclarationIdentity? {
    let ds = lookup(program[a].identifier.value, lexicallyIn: .init(node: d))
    if let pick = ds.uniqueElement {
      return pick
    } else {
      fatalError("TODO: report some error")
    }
  }

  /// Reports that `d` has no implementation.
  private mutating func reportMissingImplementation(of d: AssociatedTypeDeclaration.ID) {
    let n = program[d].identifier.value
    let m = "no implementation of associated type requirement '\(n)'"
    report(.init(.error, m, at: program.spanForDiagnostic(about: d)))
  }

  /// Returns `true` iff `r` refers to a value whose computation is pure.
  private func isStable(_ r: DeclarationReference) -> Bool {
    switch r {
    case .direct(let d):
      return isStable(d)
    default:
      return false
    }
  }

  /// Returns `true` iff `r` declares a value whose computation is pure.
  private func isStable(_ d: DeclarationIdentity) -> Bool {
    switch program.kind(of: d) {
    case AssociatedTypeDeclaration.self:
      return true
    case ConformanceDeclaration.self:
      return true
    case ExtensionDeclaration.self:
      return true
    case GenericParameterDeclaration.self:
      return true
    case ImportDeclaration.self:
      return true
    case StructDeclaration.self:
      return true
    case TraitDeclaration.self:
      return true
    case TypeAliasDeclaration.self:
      return true
    default:
      return program.parent(containing: d).node == nil
    }
  }

  // MARK: Implicit search

  /// The result of a derivation step produced by implicit resolution.
  private enum ImplicitDeduction {

    /// The type of a continuation representing the premise of resolution rule.
    typealias Continuation = (inout Typer) -> [ImplicitDeduction]

    /// Resolution failed.
    case fail

    /// Resolution succeeded.
    case done(SummonResult)

    /// Resolution requires a recursive lookup.
    case next(Continuation)

  }

  /// A witness resolved by implicit resolution.
  internal struct SummonResult {

    /// The expression of the witness.
    internal let witness: WitnessExpression

    /// A table assigning the open variables of the witness's type.
    internal let environment: SubstitutionTable

  }

  /// Returns witnesses of values of type `t` derivable from the implicit store in `scopeOfUse`.
  internal mutating func summon(
    _ t: AnyTypeIdentity, in scopeOfUse: ScopeIdentity
  ) -> [SummonResult] {
    summon(
      t, in: scopeOfUse, where: .init(), without: [t], withMaxDepth: maxImplicitDepth,
      then: { (_, ws) in ws })
  }

  /// Returns the result of `continuation` called with witnesses of values of type `t` derivable
  /// from the implicit store in `scopeOfUse`.
  ///
  /// - Parameters:
  ///   - t: The type whose instance is summoned.
  ///   - scopeOfUse: The scope in which the witnesses are resolve.
  ///   - subs: A table mapping type variables in `t` and `usings` to their values.
  ///   - usings: The types whose instances can't be summoned to resolve witneses.
  ///   - maxDepth: The maximum depth of the derivations resolve witnesses.
  ///   - continuation: A closure called with the resolve witnesses.
  private mutating func summon<T>(
    _ t: AnyTypeIdentity, in scopeOfUse: ScopeIdentity,
    where subs: SubstitutionTable,
    without usings: Set<AnyTypeIdentity>,
    withMaxDepth maxDepth: Int,
    then continuation: (inout Self, [SummonResult]) -> T
  ) -> T {
    // Did we already compute the result?
    if let table = cache.scopeToSummoned[scopeOfUse], let result = table[t] {
      return continuation(&self, result)
    }

    var ds = program.declarations(of: ConformanceDeclaration.self, lexicallyIn: scopeOfUse)

    // If there aren't any givens in `s`, just summon in the parent scope.
    if ds.isEmpty {
      let result = program.parent(containing: scopeOfUse).map({ (p) in summon(t, in: p) }) ?? []
      cache.scopeToSummoned[scopeOfUse, default: [:]][t] = result
      return continuation(&self, result)
    }

    // We can't just extend the set of candidates summoned in the outer scope as the introduction
    // of a new given may change the result of implicit resolution. Instead, we must consider all
    // visible givens at once.
    for p in program.scopes(from: scopeOfUse).dropFirst() {
      ds.append(contentsOf: program.declarations(of: ConformanceDeclaration.self, lexicallyIn: p))
    }

    var done: [SummonResult] = []
    var work: [ImplicitDeduction.Continuation] = ds.map { (d) in
      let u = declaredType(of: d)
      let w = WitnessExpression(value: .reference(.direct(.init(d))), type: u)
      return { (me) in
        me.match(w, t, in: scopeOfUse, where: subs, without: usings, withMaxDepth: maxDepth)
      }
    }

    while done.isEmpty && !work.isEmpty {
      var next: [ImplicitDeduction.Continuation] = []

      for step in work {
        for r in step(&self) {
          switch r {
          case .fail: continue
          case .done(let w): done.append(w)
          case .next(let s): next.append(s)
          }
        }
      }

      swap(&next, &work)
    }

    cache.scopeToSummoned[scopeOfUse, default: [:]][t] = done
    return continuation(&self, done)
  }

  /// Returns the result of a derivation step in the matching of `witness` with `queried`.
  private mutating func match(
    _ witness: WitnessExpression, _ queried: AnyTypeIdentity, in scopeOfUse: ScopeIdentity,
    where subs: SubstitutionTable,
    without usings: Set<AnyTypeIdentity>,
    withMaxDepth maxDepth: Int
  ) -> [ImplicitDeduction] {
    // Weak-head normal forms.
    let a = program.types.reify(witness.type, applying: subs, withVariables: .kept)
    let b = program.types.reify(queried, applying: subs, withVariables: .kept)

    // The witness has the desired type?
    if let s = program.types.unifiable(a, b) {
      return [.done(.init(witness: witness, environment: subs.union(s)))]
    }

    // The witness is a universal type?
    else if let u = program.types[a] as? UniversalType {
      var vs: [AnyTypeIdentity] = .init(minimumCapacity: u.parameters.count)
      var ss: [AnyTypeIdentity: AnyTypeIdentity] = .init(minimumCapacity: u.parameters.count)
      for p in u.parameters {
        let v = fresh().erased
        vs.append(v)
        ss[p.erased] = v
      }

      let w = WitnessExpression(
        value: .typeApplication(witness, vs),
        type: program.types.substitute(ss, in: u.body))
      let r = ImplicitDeduction.next { (me) in
        me.match(w, b, in: scopeOfUse, where: subs, without: usings, withMaxDepth: maxDepth)
      }
      return [r]
    }

    // The witness is an implication?
    else if let i = program.types[a] as? Implication, maxDepth > 0 {
      // Assume that the implication has a non-empty context.
      let (x, xs) = i.context.headAndTail!

      var us = usings
      if !us.insert(x).inserted { return [.fail] }

      let v = xs.isEmpty ? i.head : demand(Implication(context: .init(xs), head: i.head)).erased
      let r = ImplicitDeduction.next { (me) in
        me.summon(
          x, in: scopeOfUse, where: subs, without: us, withMaxDepth: maxDepth - 1
        ) { (me, arguments) in
          var rs: [ImplicitDeduction] = []
          for a in arguments {
            let w = WitnessExpression(value: .termApplication(witness, a.witness), type: v)
            let s = subs.union(a.environment)
            let m = me.match(
              w, b, in: scopeOfUse, where: s, without: usings, withMaxDepth: maxDepth)
            rs.append(contentsOf: m)
          }
          return rs
        }
      }
      return [r]
    }

    // Resolution failed.
    else { return [.fail] }
  }

  // MARK: Name resolution

  /// A candidate for resolving a name component.
  internal struct NameResolutionCandidate {

    /// The way in which the resolved entity is referred to.
    internal let reference: DeclarationReference

    /// The type of the expression referring to the resolved entity.
    internal let type: AnyTypeIdentity

  }

  private struct NameResolutionContext {

    let qualification: DeclarationReference.Qualification

    let type: AnyTypeIdentity

  }

  private mutating func resolve(
    _ e: NameExpression.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    var (unresolved, prefix) = program.components(of: e)

    var qualification: NameResolutionContext?
    switch prefix {
    case .none:
      // All components are nominal.
      qualification = nil

    case .implicit:
      // First component is implicit; use the expected type.
      if let h = context.expectedType {
        qualification = .init(qualification: .implicit, type: h)
      } else {
        report(.init(.error, "no context to resolve '\(program[e].name)'", at: program[e].site))
        return .error
      }

    case .explicit(let p):
      // First component is an arbitrary expression; use inference.
      let t = inferredType(of: p, in: &context)
      qualification = .init(qualification: .explicit(p), type: t)
    }

    let scopeOfUse = program.parent(containing: e)
    while let component = unresolved.popLast() {
      // Gather the declarations to which `c` may refer.
      let candidates: [NameResolutionCandidate]
      if let q = qualification {
        candidates = resolve(program[component].name.value, memberOf: q, visibleFrom: scopeOfUse)
      } else {
        candidates = resolve(program[component].name.value, unqualifiedIn: scopeOfUse)
      }

      // Fail if there is no candidate.
      if candidates.isEmpty {
        let n = program[component].name
        if let q = qualification {
          let m = program.format("type '%T' has no member '\(n)'", [q.type])
          report(.init(.error, m, at: n.site))
        } else {
          report(program.undefinedSymbol(n.value, at: n.site))
        }
        return .error
      }

      // TODO: Filter out inaccessible candidates

      let t = assume(component, boundTo: candidates, in: &context.obligations)
      switch program.types[t] {
      case is TypeVariable:
        // We need inference to continue.
        break

      case let t as Metatype:
        // Name resolution proceeds in the the inhabitant of the metatype rather than the metatype
        // itself so that expressions of the form `T.m` can denote entities introduced as members
        // of `T` (instead of `Metatype<T>`).
        qualification = .init(qualification: .explicit(.init(component)), type: t.inhabitant)

      default:
        // Next component should be member of `t`.
        qualification = .init(qualification: .explicit(.init(component)), type: t)
      }
    }

    if unresolved.isEmpty {
      return context.obligations.syntaxToType[e.erased]!
    } else {
      fatalError("TODO")
    }
  }

  private mutating func resolve(
    _ n: Name, unqualifiedIn scopeOfUse: ScopeIdentity
  ) -> [NameResolutionCandidate] {
    let ds = lookup(n.identifier, unqualifiedIn: scopeOfUse)

    var candidates: [NameResolutionCandidate] = []
    for d in ds {
      candidates.append(.init(reference: .direct(d), type: typeOfName(boundTo: d)))
    }

    // Predefined names are resolved iff no other candidate has been found.
    if candidates.isEmpty {
      return resolve(predefined: n, unqualifiedIn: scopeOfUse)
    } else {
      return candidates
    }
  }

  /// Resolves `n` as a predefined name unqualified in `scopeOfUse`.
  private mutating func resolve(
    predefined n: Name, unqualifiedIn scopeOfUse: ScopeIdentity
  ) -> [NameResolutionCandidate] {
    switch n.identifier {
    case "Self":
      if let t = typeOfSelf(in: scopeOfUse) {
        let u = demand(Metatype(inhabitant: t)).erased
        return [.init(reference: .predefined, type: u)]
      } else {
        return []
      }

    case "self":
      if let t = typeOfSelf(in: scopeOfUse) {
        return [.init(reference: .predefined, type: t)]
      } else {
        return []
      }

    case "Void":
      let t = demand(Metatype(inhabitant: .void)).erased
      return [.init(reference: .predefined, type: t)]

    default:
      return []
    }
  }

  private mutating func resolve(
    _ n: Name, memberOf qualification: NameResolutionContext,
    visibleFrom scopeOfUse: ScopeIdentity
  ) -> [NameResolutionCandidate] {
    let ds = lookup(n.identifier, memberOf: qualification.type, visibleFrom: scopeOfUse)

    var candidates: [NameResolutionCandidate] = []
    for d in ds {
      candidates.append(.init(reference: .direct(d), type: typeOfName(boundTo: d)))
    }

    // Native members and members declared in extensions shadow members inherited by conformance.
    if !candidates.isEmpty {
      return candidates
    }

    for (concept, ds) in lookup(n.identifier, memberOfTraitVisibleFrom: scopeOfUse) {
      let p = demand(Trait(declaration: concept)).erased
      let a = Value.type(qualification.type)
      let t = demand(TypeApplication(abstraction: p, arguments: [a])).erased
      let summonings = summon(t, in: scopeOfUse)

      // TODO: report ambiguous resolution results

      for s in summonings {
        guard let m = evaluate(s.witness).cast(as: Model.self) else { continue }
        for d in ds {
          let u = typeOfImplementation(satisfying: d, in: m)
          let c = NameResolutionCandidate(
            reference: .inherited(witness: s.witness, member: d), type: u)
          candidates.append(c)
        }
      }
    }

    return candidates
  }

  /// Returns the declarations introducing `identifier` without qualification in `scopeOfUse`.
  private mutating func lookup(
    _ identifier: String, unqualifiedIn scopeOfUse: ScopeIdentity
  ) -> [DeclarationIdentity] {
    var result: [DeclarationIdentity] = []

    /// Adds the contents of `ds` to `result` if either `result` is empty or all elements in `ds`
    /// are overloadable, and returns whether declarations from outer scopes are shadowed.
    func append(_ ds: [DeclarationIdentity]) -> Bool {
      if ds.allSatisfy(program.isOverloadable(_:)) {
        result.append(contentsOf: ds)
        return false
      } else if result.isEmpty {
        result.append(contentsOf: ds)
        return true
      } else {
        return true
      }
    }

    // Look for declarations in `scopeOfUse` and its ancestors.
    for s in program.scopes(from: scopeOfUse) {
      if append(lookup(identifier, lexicallyIn: s)) {
        return result
      }
    }

    // Look for top-level declarations in other source files.
    let f = scopeOfUse.file
    for s in program[f.module].sourceFileIdentities where s != f {
      if append(lookup(identifier, lexicallyIn: .init(file: s))) {
        return result
      }
    }

    // Look for imports.
    for n in imports(of: f) {
      result.append(contentsOf: lookup(identifier, atTopLevelOf: n))
    }
    return result
  }

  /// Returns the top-level declarations of `m` introducing `identifier`.
  private mutating func lookup(
    _ identifier: String, atTopLevelOf m: Program.ModuleIdentity
  ) -> [DeclarationIdentity] {
    if let table = cache.moduleToIdentifierToDeclaration[m] {
      return table[identifier] ?? []
    } else {
      var table = Memos.LookupTable()
      extendLookupTable(&table, with: program[m].topLevelDeclarations)
      cache.moduleToIdentifierToDeclaration[m] = table
      return table[identifier] ?? []
    }
  }

  /// Returns the declarations introducing `identifier` in `s`.
  private mutating func lookup(
    _ identifier: String, lexicallyIn s: ScopeIdentity
  ) -> [DeclarationIdentity] {
    declarations(lexicallyIn: s)[identifier] ?? []
  }

  /// Returns the declarations that introduce `identifier` as a member of `t` and that are visible
  /// from `scopeOfUse`.
  private mutating func lookup(
    _ identifier: String, memberOf t: AnyTypeIdentity,
    visibleFrom scopeOfUse: ScopeIdentity
  ) -> [DeclarationIdentity] {
    declarations(memberOf: t, visibleFrom: scopeOfUse)[identifier] ?? []
  }

  /// Returns the declarations that introduce `identifier` as a member of a trait that is visible
  /// from `scopeOfUse`.
  private mutating func lookup(
    _ identifier: String, memberOfTraitVisibleFrom scopeOfUse: ScopeIdentity
  ) -> [(concept: TraitDeclaration.ID, members: [DeclarationIdentity])] {
    var result: [(concept: TraitDeclaration.ID, members: [DeclarationIdentity])] = []
    for d in traits(visibleFrom: scopeOfUse) {
      let ms = lookup(identifier, lexicallyIn: .init(node: d))
      if !ms.isEmpty {
        result.append((concept: d, members: ms))
      }
    }
    return result
  }

  /// Returns the declarations that introduce a member of `t` and are visible from `s`.
  private mutating func declarations(
    memberOf t: AnyTypeIdentity, visibleFrom s: ScopeIdentity
  ) -> Memos.LookupTable {
    // Higher-kinded types have no members.
    if program.isHigherKinded(t) { return .init() }

    // Did we already compute a lookup table?
    if let table = cache.scopeToTypeToLookupTable[Scoped(t, in: s)] {
      return table
    }

    // Are we in the scope of a syntax tree?
    else if let p = program.parent(containing: s) {
      var table = declarations(memberOf: t, visibleFrom: p)
      for d in extensions(lexicallyIn: s)
      where !declarationsOnStack.contains(.init(d)) && applies(d, to: t) {
        extendLookupTable(&table, with: program[d].members)
      }
      cache.scopeToTypeToLookupTable[Scoped(t, in: s)] = table
      return table
    }

    // We are at the top-level.
    else {
      var table = declarations(nativeMembersOf: t)
      let ms = imports(of: s.file) + [s.file.module]
      for m in ms {
        for d in program.collect(ExtensionDeclaration.self, in: program[m].topLevelDeclarations)
        where !declarationsOnStack.contains(.init(d)) && applies(d, to: t) {
          extendLookupTable(&table, with: program[d].members)
        }
      }
      cache.scopeToTypeToLookupTable[Scoped(t, in: s)] = table
      return table
    }
  }

  /// Returns the declarations lexically contained in the declaration of `t`.
  private mutating func declarations(nativeMembersOf t: AnyTypeIdentity) -> Memos.LookupTable {
    switch program.types[t] {
    case let u as Struct:
      return declarations(lexicallyIn: .init(node: u.declaration))
    case let u as TypeAlias:
      return declarations(nativeMembersOf: u.aliasee)
    default:
      return .init()
    }
  }

  /// Returns the declarations lexically contained in `s`.
  private mutating func declarations(lexicallyIn s: ScopeIdentity) -> Memos.LookupTable {
    if let table = cache.scopeToLookupTable[s] {
      return table
    } else {
      var table = Memos.LookupTable()
      extendLookupTable(&table, with: program.declarations(lexicallyIn: s))
      cache.scopeToLookupTable[s] = table
      return table
    }
  }

  /// Returns the extensions that are lexically contained in `s`.
  private mutating func extensions(lexicallyIn s: ScopeIdentity) -> [ExtensionDeclaration.ID] {
    if let ds = cache.scopeToExtensions[s] {
      return ds
    } else {
      let ds = program.declarations(of: ExtensionDeclaration.self, lexicallyIn: s)
      cache.scopeToExtensions[s] = ds
      return ds
    }
  }

  /// Returns `true` iff `d` is an extension of `t`.
  private mutating func applies(_ d: ExtensionDeclaration.ID, to t: AnyTypeIdentity) -> Bool {
    extendeeType(d) == t
  }

  /// Returns the modules that are imported by `f`, which is in the module being typed.
  private mutating func imports(
    of f: Program.SourceFileIdentity
  ) -> [Program.ModuleIdentity] {
    if let table = cache.sourceToImports[f.offset] {
      return table
    } else {
      var table: [Program.ModuleIdentity] = []
      for d in program[f].topLevelDeclarations {
        // Imports precede all other declarations.
        guard let i = program.cast(d, to: ImportDeclaration.self) else { break }
        // Ignore invalid imports.
        if let m = program.identity(module: program[i].identifier.value) { table.append(m) }
      }
      cache.sourceToImports[f.offset] = table
      return table
    }
  }

  /// Extends `m` so that it maps identifiers declared in `ds` to their declarations.
  private func extendLookupTable<T: Sequence<DeclarationIdentity>>(
    _ m: inout Memos.LookupTable, with ds: T
  ) {
    for d in ds {
      // Is `d` a binding declaration?
      if let b = program.cast(d, to: BindingDeclaration.self) {
        program.forEachVariable(introducedBy: b) { (v, _) in
          m[program[v].identifier.value, default: []].append(.init(v))
        }
      }

      // Is `d` declaraing a single entity?
      else if let n = program.name(of: d) {
        m[n.identifier, default: []].append(d)
      }
    }
  }

  /// Returns the type defining the nominal scope that includes `s`, if any.
  private mutating func nominalScope(including s: ScopeIdentity) -> AnyTypeIdentity? {
    // Exit early if `s` is a file.
    guard let n = s.node else { return nil }

    // Only types have nominal scopes.
    switch program.kind(of: n) {
    case StructDeclaration.self:
      return demand(Struct(declaration: castUnchecked(n))).erased
    case TraitDeclaration.self:
      return demand(Trait(declaration: castUnchecked(n))).erased
    default:
      return nil
    }
  }

  /// Returns the declarations of the traits that are visible from `scopeOfUse`.
  private mutating func traits(
    visibleFrom scopeOfUse: ScopeIdentity
  ) -> [TraitDeclaration.ID] {
    if let ts = cache.scopeToTraits[scopeOfUse] {
      return ts
    }

    // Are we in the scope of a syntax tree?
    else if let p = program.parent(containing: scopeOfUse) {
      let ds = program.declarations(lexicallyIn: scopeOfUse)
      var ts = traits(visibleFrom: p)
      ts.append(contentsOf: program.collect(TraitDeclaration.self, in: ds))
      cache.scopeToTraits[scopeOfUse] = ts
      return ts
    }

    // We are at the top-level.
    else {
      let ds = program[scopeOfUse.file.module].topLevelDeclarations
      var ts = program.collect(TraitDeclaration.self, in: ds)
      for m in imports(of: scopeOfUse.file) {
        ts.append(
          contentsOf: program.collect(TraitDeclaration.self, in: program[m].topLevelDeclarations))
      }
      cache.scopeToTraits[scopeOfUse] = ts
      return ts
    }
  }

  // MARK: Helpers

  /// Returns the type of values expected to be returned or projected in `s`, or `nil` if `s` is
  /// not in the body of a function or subscript.
  private mutating func expectedOutputType(in s: ScopeIdentity) -> AnyTypeIdentity? {
    for t in program.scopes(from: s) {
      guard let n = t.node else { break }
      switch program.kind(of: n) {
      case FunctionDeclaration.self:
        return expectedOutputType(in: program.castUnchecked(n, to: FunctionDeclaration.self))
      case InitializerDeclaration.self:
        return .void
      default:
        continue
      }
    }
    return nil
  }

  /// Returns the type of values expected to be returned from `d`.
  private mutating func expectedOutputType(in d: FunctionDeclaration.ID) -> AnyTypeIdentity {
    let t = declaredType(of: d)
    if let a = program.types[program.types.head(t)] as? Arrow {
      return a.output
    } else {
      return .error
    }
  }

  /// Reports the diagnostic `d`.
  private mutating func report(_ d: Diagnostic) {
    program[module].addDiagnostic(d)
  }

  /// Reports the diagnostics in `ds`.
  private mutating func report<S: Sequence<Diagnostic>>(_ ds: S) {
    program[module].addDiagnostics(ds)
  }

  /// Returns the unique identity of a tree that is equal to `t`.
  private mutating func demand<T: TypeTree>(_ t: T) -> T.ID {
    program.types.demand(t)
  }

  /// Returns the unique identity of a type tree representing the metatype of `t`.
  private mutating func metatype<T: TypeTree>(of t: T) -> Metatype.ID {
    let n = demand(t).erased
    return demand(Metatype(inhabitant: n))
  }

  /// Returns the identity of a fresh type variable.
  public mutating func fresh() -> TypeVariable.ID {
    defer { nextFreshIdentifier += 1 }
    return .init(uncheckedFrom: AnyTypeIdentity(variable: nextFreshIdentifier))
  }

  /// Returns `n` assuming it identifies a node of type `U`.
  private func castUnchecked<T: SyntaxIdentity, U: Syntax>(_ n: T, to: U.Type = U.self) -> U.ID {
    program.castUnchecked(n, to: U.self)
  }

  /// Returns the result of `action` called with a projection of `self` in which `d` is in the set
  /// of extensions to ignore during name resolution.
  private mutating func ignoring<T>(
    _ d: ExtensionDeclaration.ID, _ action: (inout Self) -> T
  ) -> T {
    declarationsOnStack.insert(.init(d))
    defer { declarationsOnStack.remove(.init(d)) }
    return action(&self)
  }

}
