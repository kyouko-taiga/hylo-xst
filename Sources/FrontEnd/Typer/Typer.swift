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
    var scopeToSummoned: [ScopeIdentity: [AnyTypeIdentity: [DeclarationReference]]]

    /// The cache of `Typer.typeOfSelf(in:)`.
    var scopeToTypeOfSelf: [ScopeIdentity: AnyTypeIdentity?]

    /// The cache of `Typer.possiblyPartialStaticContext(of:)`.
    var declarationToStaticContext: [DeclarationIdentity: StaticContext]

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
      self.declarationToStaticContext = [:]
    }

  }

  // MARK: Type relations

  /// Returns the canonical form of `t`.
  public func canonical(_ t: AnyTypeIdentity) -> AnyTypeIdentity {
    if !t[.notCanonical] { return t }

    switch program.types[t] {
    case let u as TypeAlias:
      return u.aliasee
    default:
      program.unexpected(t)
    }
  }

  /// Returns `true` iff `t` and `u` are equal.
  public func equal(_ t: AnyTypeIdentity, _ u: AnyTypeIdentity) -> Bool {
    (t == u) || program.types[canonical(t)].equals(program.types[canonical(u)])
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
        report(.init(.error, "duplicate declaration", at: program[v].site))
      }
    }
  }

  /// Type checks `d`.
  private mutating func check(_ d: ConformanceDeclaration.ID) {
    _ = declaredType(of: d)
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
    if let a = program.types[t] as? Arrow {
      for p in program[d].parameters { check(p) }
      check(body: program[d].body, of: .init(d), expectingResultOfType: a.output)
    }
  }

  /// Type checks `d`.
  private mutating func check(_ d: InitializerDeclaration.ID) {
    let t = declaredType(of: d)

    // Nothing more to do if the declaration doesn't have an arrow type.
    if let a = program.types[t] as? Arrow {
      for p in program[d].parameters { check(p) }
      check(body: program[d].body, of: .init(d), expectingResultOfType: a.output)
    }
  }

  /// Type checks `body` as the definition of `d`, which declares a function or susbscript that
  /// outputs an instance of `r`.
  private mutating func check(
    body: [StatementIdentity]?, of d: DeclarationIdentity,
    expectingResultOfType r: AnyTypeIdentity
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
    _ = declaredType(of: d)
    // TODO
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
    return s.substitutions.reify(t)
  }

  /// Type checks `e` expecting it to have type `r` and reporting an error if it doesn't.
  private mutating func check(_ e: ExpressionIdentity, expecting r: AnyTypeIdentity) {
    let u = check(e, inContextExpecting: r)
    if (u != r) && (canonical(u) != .never) && !u[.hasError] {
      let m = program.format("expected '%T', found '%T'", [r, u])
      report(.init(.error, m, at: program[e].site))
    }
  }

  /// Type checks `e`, which occurs as a statement.
  private mutating func checkAsStatement(_ e: ExpressionIdentity) {
    let u = check(e, inContextExpecting: .void)
    if (canonical(u) != .void) && !u[.hasError] {
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
    } else if canonical(u) != .void {
      let m = program.format("expected value of type '%T'", [u])
      let s = program.spanForDiagnostic(about: s)
      report(.init(.error, m, at: s))
    }

    program[module].setType(.void, for: s)
  }

  /// Builds and type checks the static context of `d`.
  private mutating func checkStaticContext(of d: FunctionDeclaration.ID) {
    _ = staticContext(of: d)
  }

  /// Builds and returns the static context of `d`
  ///
  /// The returned context is partially formed if this method is called during the the context's
  /// construction.
  private mutating func possiblyPartialStaticContext(of d: DeclarationIdentity) -> StaticContext {
    if let c = cache.declarationToStaticContext[d] {
      return c
    } else {
      return staticContext(of: d)
    }
  }

  /// Builds and returns the static context of `d`, which is a generic declaration.
  private mutating func staticContext(of d: DeclarationIdentity) -> StaticContext {
    switch program.kind(of: d) {
    default:
      program.unexpected(d)
    }
  }

  /// Builds and returns the static context of `d`.
  private mutating func staticContext(of d: FunctionDeclaration.ID) -> StaticContext {
    if let c = program[module].staticContext(of: d) { return c }
    var partialContext = StaticContext()

    for p in program[d].staticParameters.implicit {
      if let t = declaredType(of: p).unlessError {
        partialContext.add(.abstract(type: program.types.castUnchecked(t)))
      }
      cache.declarationToStaticContext[.init(d)] = partialContext
    }

    program[module].setStaticContext(partialContext, for: d)
    return partialContext
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

    var t = typeOfSelf(in: program.parent(containing: d))!
    t = demand(AssociatedType(declaration: d, qualification: t)).erased
    t = demand(Metatype(inhabitant: t)).erased
    program[module].setType(t, for: d)
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
      let u = s.substitutions.reify(p)

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

    let t = declaredConformanceType(program[d].extendee, program[d].concept)
    program[module].setType(t, for: d)
    return t
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: FunctionDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[module].type(assignedTo: d) { return memoized }

    checkStaticContext(of: d)

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
    let t = demand(a).erased
    program[module].setType(t, for: d)
    return t
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: GenericParameterDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[module].type(assignedTo: d) { return memoized }

    let t = demand(TypeParameter(declaration: d)).erased
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
              label: program[v].identifier.value, type: u,
              hasDefault: false,
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

    let t = demand(Struct(declaration: d)).erased
    let u = demand(Metatype(inhabitant: t)).erased
    program[module].setType(u, for: d)
    return u
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: TraitDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[module].type(assignedTo: d) { return memoized }

    let t = demand(Trait(declaration: d)).erased
    let u = demand(Metatype(inhabitant: t)).erased
    program[module].setType(u, for: d)
    return u
  }


  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: TypeAliasDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[module].type(assignedTo: d) { return memoized }

    // Is it the first time we enter this method for `d`?
    if declarationsOnStack.insert(.init(d)).inserted {
      defer { declarationsOnStack.remove(.init(d)) }

      switch canonical(evaluateTypeAscription(program[d].aliasee)) {
      case .error:
        program[module].setType(.error, for: d)
        return .error
      case let aliasee:
        let t = demand(TypeAlias(declaration: d, aliasee: aliasee)).erased
        let u = demand(Metatype(inhabitant: t)).erased
        program[module].setType(u, for: d)
        return u
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
          label: program[p].label?.value,
          type: declaredType(of: p),
          hasDefault: false,
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

    if f.isVariable || (program.types[f] is any Callable) {
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
      return assume(e, hasType: o, in: &context.obligations)
    }

    // Was the error already reported?
    else if f == .error {
      return assume(e, hasType: .error, in: &context.obligations)
    }

    // The callee cannot be applied.
    else {
      report(program.cannotCall(f, program[e].style, at: program[program[e].callee].site))
      return assume(e, hasType: .error, in: &context.obligations)
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
      program[module].replace(.init(e), for: program[e].clone(callee: .init(n)))
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
    var t = evaluateTypeAscription(program[e].projectee)
    t = demand(RemoteType(projectee: t, access: program[e].access.value)).erased
    t = demand(Metatype(inhabitant: t)).erased
    return assume(e, hasType: t, in: &context.obligations)
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

    let r = demand(Tuple(elements: ts))
    return assume(e, hasType: r.erased, in: &context.obligations)
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
      return assume(d, hasType: t, in: &context.obligations)
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

    return assume(d, hasType: p, in: &context.obligations)
  }

  /// Returns the inferred type of `d`, which occurs in `context`.
  private mutating func inferredType(
    of d: VariableDeclaration.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let t = fresh().erased
    return assume(d, hasType: t, in: &context.obligations)
  }

  /// Constrains the name component in `r` to be a reference to one of `r`'s resolution candidates
  /// in `o`, and returns the inferred type of `r`.
  private mutating func assume(
    _ n: NameExpression.ID, isBoundTo cs: [NameResolutionCandidate], in o: inout Obligations
  ) -> AnyTypeIdentity {
    // If there's only one candidate, we're done.
    if let pick = cs.uniqueElement {
      // TODO: Instantiate

      o.assume(n, isBoundTo: pick.reference)
      if let t = program.types[pick.type] as? RemoteType {
        return assume(n, hasType: t.projectee, in: &o)
      } else {
        return assume(n, hasType: pick.type, in: &o)
      }
    }

    fatalError("TODO")
  }

  /// Constrains `n` to have type `t` in `o` and returns `t`.
  @discardableResult
  private mutating func assume<T: SyntaxIdentity>(
    _ n: T, hasType t: AnyTypeIdentity, in o: inout Obligations
  ) -> AnyTypeIdentity {
    if let u = o.syntaxToType[n.erased] {
      o.assume(TypeEquality(lhs: t, rhs: u, site: program[n].site))
    } else {
      o.assume(.init(n), instanceOf: t)
    }

    if t[.hasError] { o.setUnsatisfiable() }
    return t
  }

  /// Proves the obligations `o`, which relate to the well-typedness of `n`, returning the best
  /// assignment of universally quantified variables.
  @discardableResult
  private mutating func discharge<T: SyntaxIdentity>(
    _ o: Obligations, relatedTo n: T
  ) -> Solution {
    if o.constraints.isEmpty {
      let s = Solution(substitutions: .init(), bindings: o.bindings)
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
    for (n, t) in o.syntaxToType {
      program[module].setType(t, for: n)
    }
    for (n, r) in s.bindings {
      program[module].bind(n, to: r)
    }
  }

  // MARK: Compile-time evaluation

  /// Returns the value of `e` evaluated as a type ascription.
  private mutating func evaluateTypeAscription(_ e: ExpressionIdentity) -> AnyTypeIdentity {
    var c = InferenceContext()
    let t = inferredType(of: e, in: &c)
    let s = discharge(c.obligations, relatedTo: e)
    let u = s.substitutions.reify(t)

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

  /// Returns the value of the declaration referred to by `r`.
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
    guard let (concept, _) = program.types.castToTraitApplication(t) else {
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

  /// Returns the declarations of values in the implicit store of `s` and having type `t`.
  private mutating func summon(
    _ t: AnyTypeIdentity, in s: ScopeIdentity
  ) -> [DeclarationReference] {
    // Did we already compute the result?
    if let table = cache.scopeToSummoned[s], let cs = table[t] {
      return cs
    }

    var ds = program.declarations(of: ConformanceDeclaration.self, lexicallyIn: s)

    // If there aren't any givens in `s`, just summon in the parent scope.
    if ds.isEmpty {
      let cs = program.parent(containing: s).map({ (p) in summon(t, in: p) }) ?? []
      cache.scopeToSummoned[s, default: [:]][t] = cs
      return cs
    }

    // We can't just extend the set of candidates summoned in the outer scope as the introduction
    // of a new given may change the result of implicit resolution. Instead, we must consider all
    // visible givens at once.
    for p in program.scopes(from: s).dropFirst() {
      ds.append(contentsOf: program.declarations(of: ConformanceDeclaration.self, lexicallyIn: p))
    }

    var cs: [DeclarationReference] = []

    for d in ds {
      // `u` is a trait application `P<T>` or a universal type or an implicit function type.
      // Otherwise `declaredType(of:)` returned an error because `d` is ill-formed.
      let u = declaredType(of: d)

      if equal(u, t) {
        cs.append(.direct(.init(d)))
      } else {
        // TODO: conditional and universal conformances
      }
    }

    // TODO: conditional and universal conformances

    cache.scopeToSummoned[s, default: [:]][t] = cs
    return cs
  }

  /// Returns the models given as compile-time arguments in `s`.
  private mutating func models(givenIn s: ScopeIdentity) -> [Model] {
    return []
//    guard let n = s.node else { return [] }
//
//    switch program.kind(of: n) {
//    case FunctionDeclaration.self:
//      return possiblyPartialStaticContext(of: .init(uncheckedFrom: n)).givens
//    default:
//      return []
//    }
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

  // MARK: Name resolution

  /// A candidate for resolving a name component.
  private struct NameResolutionCandidate {

    /// The way in which the resolved entity is referred to.
    let reference: DeclarationReference

    /// The type of the expression referring to the resolved entity.
    let type: AnyTypeIdentity

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

      let t = assume(component, isBoundTo: candidates, in: &context.obligations)
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
      candidates.append(.init(reference: .direct(d), type: declaredType(of: d)))
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
      candidates.append(.init(reference: .direct(d), type: declaredType(of: d)))
    }

    // Native members and members declared in extensions shadow members inherited by conformance.
    if !candidates.isEmpty {
      return candidates
    }

    for (concept, ds) in lookup(n.identifier, memberOfTraitVisibleFrom: scopeOfUse) {
      let p = demand(Trait(declaration: concept)).erased
      let a = Value.type(qualification.type)
      let t = demand(TypeApplication(abstraction: p, arguments: [a])).erased
      let definitions = summon(t, in: scopeOfUse)

      // TODO: report ambiguous resolution results

      for n in definitions {
        guard let witness = evaluate(n).cast(as: Model.self) else { continue }
        for d in ds {
          let u = typeOfImplementation(satisfying: d, in: witness)
          let c = NameResolutionCandidate(reference: .inherited(witness: n, member: d), type: u)
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
    let a = declaredType(of: d)
    return (program.types[a] as? Arrow)?.output ?? .error
  }

  /// Reports the diagnostic `d`.
  private mutating func report(_ d: Diagnostic) {
    program[module].addDiagnostic(d)
  }

  /// Returns the unique identity of a tree that is equal to `t`.
  private mutating func demand<T: TypeTree>(_ t: T) -> T.ID {
    program.types.demand(t)
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
