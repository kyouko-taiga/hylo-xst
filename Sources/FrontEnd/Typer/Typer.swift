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

    /// The cache of `Typer.traits(visibleFrom:)`
    var scopeToTraits: [ScopeIdentity: [TraitDeclaration.ID]]

    /// The cache of `Typer.summon(_:in:)`.
    var scopeToSummoned: [ScopeIdentity: [AnyTypeIdentity: [SummonResult]]]

    /// The cache of `Typer.typeOfSelf(in:)`.
    var scopeToTypeOfSelf: [ScopeIdentity: AnyTypeIdentity?]

    /// The cache of `Typer.aliasesInConformance(seenThrough:)`.
    var witnessToAliases: [WitnessExpression: [AnyTypeIdentity: AnyTypeIdentity]]

    /// Creates an instance for typing `m`, which is a module in `p`.
    init(typing m: Program.ModuleIdentity, in p: Program) {
      self.moduleToIdentifierToDeclaration = .init(repeating: nil, count: p.modules.count)
      self.sourceToImports = .init(repeating: nil, count: p[m].sources.count)
      self.scopeToExtensions = [:]
      self.scopeToLookupTable = [:]
      self.scopeToTraits = [:]
      self.scopeToSummoned = [:]
      self.scopeToTypeOfSelf = [:]
      self.witnessToAliases = [:]
    }

  }

  // MARK: Type relations

  /// Returns `true` iff `t` and `u` are equal.
  public mutating func equal(_ t: AnyTypeIdentity, _ u: AnyTypeIdentity) -> Bool {
    // Fast path: both types are trivially equal.
    if t == u { return true }

    // Slow path: remove aliases.
    return program.types.dealiased(t) == program.types.dealiased(u)
  }

  /// Returns `true` iff `t` and `u` are equal modulo α-conversion.
  public func unifiable(_ t: AnyTypeIdentity, _ u: AnyTypeIdentity) -> Bool {
    program.types.unifiable(t, u) != nil
  }

  // MARK: Type checking

  /// Type checks `d`.
  private mutating func check(_ d: DeclarationIdentity) {
    switch program.tag(of: d) {
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
    let t = declaredType(of: d)

    check(program[d].contextParameters)
    for m in program[d].members { check(m) }

    // Nothing else to do if the declaration is abstract.
    if program[d].isAbstract { return }

    let witness = program.types.head(t)
    guard let (c, conformer) = program.types.castToTraitApplication(witness) else {
      assert(t == .error)
      return
    }

    let concept = program.types[c].declaration
    let requirements = program[concept].members
    var substitutions = [typeOfSelf(in: concept): conformer]

    // Find the implementations of associated types.
    for r in program.collect(AssociatedTypeDeclaration.self, in: requirements) {
      let value = implementation(of: r, in: d).map({ (i) in declaredType(of: i) }) ?? .error

      if let m = program.types[value] as? Metatype {
        let k0 = declaredType(of: r)
        let k1 = program.types[k0] as! Metatype
        substitutions[k1.inhabitant] = m.inhabitant
      } else {
        return reportMissingImplementation(of: r)
      }
    }

    // Check that other requirements may be satisfied. We do not need to store the implementations
    // since witness tables are built on demand.
    for r in requirements {
      switch program.tag(of: r) {
      case FunctionDeclaration.self:
        _ = implementation(
          of: program.castUnchecked(r, to: FunctionDeclaration.self), in: concept,
          for: conformer, applying: substitutions, in: d)

      default:
        continue
      }
    }
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
    for m in program[d].members { check(m) }
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
    switch program.tag(of: d) {
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

  /// Returns the declaration implementing `requirement` in `d`, if any.
  private mutating func implementation(
    of requirement: AssociatedTypeDeclaration.ID, in d: ConformanceDeclaration.ID
  ) -> DeclarationIdentity? {
    lookup(program[requirement].identifier.value, lexicallyIn: .init(node: d)).uniqueElement
  }

  /// Returns the declarations implementing `requirement` in `d`, if any.
  private mutating func implementation(
    of r: FunctionDeclaration.ID, in c: TraitDeclaration.ID,
    for t: AnyTypeIdentity,
    applying ss: [AnyTypeIdentity: AnyTypeIdentity], in d: ConformanceDeclaration.ID
  ) -> DeclarationReference? {
    let n = program.name(of: r)
    let u = declaredType(of: r)
    let expectedType = program.types.substitute(ss, in: program.types.bodyAndContext(u).body)
    let scopeOfUse = ScopeIdentity(node: d)
    var viable: [DeclarationReference] = []

    // Is there a unique implementation in the conformance declaration?
    for d in lookup(n.identifier, lexicallyIn: .init(node: d)) {
      let u = declaredType(of: d)
      if unifiable(u, expectedType) { viable.append(.direct(d)) }
    }

    if let pick = viable.uniqueElement {
      return pick
    } else if !viable.isEmpty {
      reportAmbiguousImplementation(of: r, in: d)
      return nil
    }

    // Is there an implementation that is already member of the conforming type?
    for c in resolve(n, memberOf: .init(value: .virtual, type: t), visibleFrom: scopeOfUse) {
      if !unifiable(c.type, expectedType) { continue }

      switch c.reference {
      case .inherited(_, .init(r)) where program[r].body == nil:
        continue
      default:
        viable.append(c.reference)
      }
    }

    if let pick = viable.uniqueElement {
      return pick
    } else {
      if viable.isEmpty {
        reportMissingImplementation(of: r, in: d)
      } else {
        reportAmbiguousImplementation(of: r, in: d)
      }
      return nil
    }
  }

  /// Reports that `requirement` has no implementation.
  private mutating func reportMissingImplementation(of requirement: AssociatedTypeDeclaration.ID) {
    let n = program[requirement].identifier.value
    let m = "no implementation of associated type requirement '\(n)'"
    report(.init(.error, m, at: program.spanForDiagnostic(about: requirement)))
  }

  /// Reports that `requirement` has no implementation.
  private mutating func reportMissingImplementation(
    of requirement: FunctionDeclaration.ID,
    in conformance: ConformanceDeclaration.ID
  ) {
    let n = program.name(of: requirement)
    let m = "no implementation of '\(n)'"
    report(.init(.error, m, at: program.spanForDiagnostic(about: conformance)))
  }

  /// Reports that `requirement` has multiple equally valid implementations.
  private mutating func reportAmbiguousImplementation(
    of requirement: FunctionDeclaration.ID,
    in conformance: ConformanceDeclaration.ID
  ) {
    let n = program.name(of: requirement)
    let m = "ambiguous implementation of '\(n)'"
    report(.init(.error, m, at: program.spanForDiagnostic(about: conformance)))
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
    if !equal(u, r) && !equal(u, .never) && !u[.hasError] {
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
    switch program.tag(of: s) {
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
    switch program.tag(of: d) {
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
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    let t = typeOfSelf(in: program.parent(containing: d))!
    let u = metatype(of: AssociatedType(declaration: d, qualification: t)).erased
    program[module].setType(u, for: d)
    return u
  }

  /// Returns the declared type of `d`, using inference if necessary.
  private mutating func declaredType(of d: BindingDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

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
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    let t = declaredConformanceType(program[d].extendee, program[d].concept)
    let u = introduce(program[d].contextParameters, into: t)
    program[module].setType(u, for: d)
    return u
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: FunctionDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    let inputs = declaredTypes(of: program[d].parameters)
    let output = program[d].output.map({ (a) in evaluateTypeAscription(a) }) ?? .void

    var result: AnyTypeIdentity
    if program.isMember(d) {
      let p = program.parent(containing: d)
      let receiver = typeOfSelf(in: p)!
      let context = contextOfSelf(in: p)!

      var e = demand(RemoteType(projectee: receiver, access: program[d].effect.value)).erased
      e = demand(Tuple(elements: [.init(label: "self", type: e)])).erased

      result = demand(Arrow(environment: e, inputs: inputs, output: output)).erased
      result = introduce(program[d].contextParameters, into: result)
      result = program.types.introduce(context, into: result)
    } else {
      result = demand(Arrow(environment: .void, inputs: inputs, output: output)).erased
      result = introduce(program[d].contextParameters, into: result)
    }

    program[module].setType(result, for: d)
    return result
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: GenericParameterDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    let t = metatype(of: GenericParameter(declaration: d)).erased
    program[module].setType(t, for: d)
    return t
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: InitializerDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

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
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    let t = program[d].ascription.map({ (a) in evaluateTypeAscription(.init(a)) }) ?? {
      report(.init(.error, "parameter requires ascription", at: program[d].site))
      return .error
    }()

    program[module].setType(t, for: d)
    return t
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: StructDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    let t = metatype(of: Struct(declaration: d)).erased
    program[module].setType(t, for: d)
    return t
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: TraitDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    let t = metatype(of: Trait(declaration: d)).erased
    program[module].setType(t, for: d)
    return t
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: TypeAliasDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

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
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

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
          declaration: p, label: program[p].label?.value, type: declaredType(of: p),
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

  /// Returns the type of `requirement` seen through a conformance witnessed by `witness`.
  private mutating func declaredType(
    of requirement: DeclarationIdentity, seenThrough witness: WitnessExpression
  ) -> AnyTypeIdentity {
    let subs = aliasesInConformance(seenThrough: witness)
    let member = declaredType(of: requirement)
    let (memberSansContext, _) = program.types.bodyAndContext(member)
    return program.types.substitute(subs, in: memberSansContext)
  }

  /// Returns a table mapping the abstract types to their implementations in the conformance
  /// witnessed by `witness`.
  private mutating func aliasesInConformance(
    seenThrough witness: WitnessExpression
  ) -> [AnyTypeIdentity: AnyTypeIdentity] {
    if let memoized = cache.witnessToAliases[witness] { return memoized }

    let (c, conformer) = program.types.castToTraitApplication(witness.type)!
    let concept = program.types[c].declaration
    var subs = [typeOfSelf(in: concept): conformer]

    for r in program[concept].members {
      if let a = program.cast(r, to: AssociatedTypeDeclaration.self) {
        let i = typeOfImplementation(satisfying: a, in: witness)
        if let m = program.types[i] as? Metatype {
          let k0 = declaredType(of: r)
          let k1 = program.types[k0] as! Metatype
          subs[k1.inhabitant] = m.inhabitant
        }
      }
    }

    assert(!witness.hasVariable)
    cache.witnessToAliases[witness] = subs
    return subs
  }

  /// Returns the type that `d` extends.
  private mutating func extendeeType(_ d: ExtensionDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    let t = ignoring(d, { (me) in me.evaluateTypeAscription(me.program[d].extendee) })
    let u = introduce(program[d].contextParameters, into: t)
    program[module].setType(u, for: d)
    return u
  }

  /// Returns `t` as the head of a universal type and/or implication introducing `parameters`.
  private mutating func introduce(
    _ parameters: StaticParameters, into t: AnyTypeIdentity
  ) -> AnyTypeIdentity {
    if parameters.isEmpty { return t }

    let ps = parameters.explicit.compactMap { (p) in
      let t = declaredType(of: p)
      return program.types
        .select(\Metatype.inhabitant, on: t)
        .flatMap({ (m) in program.types.cast(m, to: GenericParameter.self) })
    }
    let us = parameters.implicit.map({ (p) in declaredType(of: p) })
    return program.types.introduce(.init(parameters: ps, usings: us), into: t)
  }

  /// Ascribes `t` to `p` and its children, reporting an error if `t` doesn't match `p`'s shape.
  private mutating func ascribe(_ t: AnyTypeIdentity, to p: PatternIdentity) {
    switch program.tag(of: p) {
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
    switch program.tag(of: e) {
    case BooleanLiteral.self:
      return inferredType(of: castUnchecked(e, to: BooleanLiteral.self), in: &context)
    case Call.self:
      return inferredType(of: castUnchecked(e, to: Call.self), in: &context)
    case NameExpression.self:
      return inferredType(of: castUnchecked(e, to: NameExpression.self), in: &context)
    case RemoteTypeExpression.self:
      return inferredType(of: castUnchecked(e, to: RemoteTypeExpression.self), in: &context)
    case StaticCall.self:
      return inferredType(of: castUnchecked(e, to: StaticCall.self), in: &context)
    case TupleLiteral.self:
      return inferredType(of: castUnchecked(e, to: TupleLiteral.self), in: &context)
    case TupleTypeExpression.self:
      return inferredType(of: castUnchecked(e, to: TupleTypeExpression.self), in: &context)
    case WildcardTypeLiteral.self:
      return inferredType(of: castUnchecked(e, to: WildcardTypeLiteral.self), in: &context)
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
    guard let f = inferredType(calleeOf: e, in: &context).unlessError else {
      return context.obligations.assume(e, hasType: .error, at: program[e].site)
    }

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
    of e: StaticCall.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    // Abstraction is inferred in the same inference context.
    guard let f = inferredType(of: program[e].callee, in: &context).unlessError else {
      return context.obligations.assume(e, hasType: .error, at: program[e].site)
    }

    let i = program[e].arguments.map { (a) in
      context.withSubcontext { (ctx) in inferredType(of: a, in: &ctx) }
    }
    let o = context.expectedType ?? fresh().erased
    let k = StaticCallConstraint(
      callee: f, arguments: i, output: o, origin: e, site: program[e].site)

    context.obligations.assume(k)
    return context.obligations.assume(e, hasType: o, at: program[e].site)
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

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: WildcardTypeLiteral.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    if let t = context.expectedType, program.types.tag(of: t) == Metatype.self {
      return context.obligations.assume(e, hasType: t, at: program[e].site)
    } else {
      let t = fresh().erased
      let u = demand(Metatype(inhabitant: t)).erased
      return context.obligations.assume(e, hasType: u, at: program[e].site)
    }
  }

  /// Returns the inferred type of `p`, which occurs in `context`.
  private mutating func inferredType(
    of p: PatternIdentity, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    switch program.tag(of: p) {
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
      let u = program.types.reify(t, applying: s.substitutions)
      program[module].setType(u, for: n)
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

  /// Returns the type of an instance of `Self` in `s`, or `nil` if `s` isn't notionally in the
  /// scope of a type declaration.
  private mutating func typeOfSelf(in s: ScopeIdentity) -> AnyTypeIdentity? {
    if let memoized = cache.scopeToTypeOfSelf[s] { return memoized }

    guard let n = s.node else { return nil }
    let result: AnyTypeIdentity?

    switch program.tag(of: n) {
    case ConformanceDeclaration.self:
      result = typeOfSelf(in: program.castUnchecked(n, to: ConformanceDeclaration.self))
    case ExtensionDeclaration.self:
      result = typeOfSelf(in: program.castUnchecked(n, to: ExtensionDeclaration.self))
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

  /// Returns the type of an instance of `Self` in `s`.
  private mutating func typeOfSelf(in d: ConformanceDeclaration.ID) -> AnyTypeIdentity {
    let t = declaredType(of: d)
    return program.types.castToTraitApplication(program.types.head(t))?.subject ?? .error
  }

  /// Returns the type of an instance of `Self` in `s`.
  private mutating func typeOfSelf(in d: ExtensionDeclaration.ID) -> AnyTypeIdentity {
    let t = extendeeType(d)
    return program.types.head(t)
  }

  /// Returns the type of an instance of `Self` in `s`.
  private mutating func typeOfSelf(in d: StructDeclaration.ID) -> AnyTypeIdentity {
    let t = declaredType(of: d)
    return (program.types[t] as? Metatype)?.inhabitant ?? .error
  }

  /// Returns the type of an instance of `Self` in `s`.
  private mutating func typeOfSelf(in d: TraitDeclaration.ID) -> AnyTypeIdentity {
    let t = declaredType(of: program[d].conformer)
    return (program.types[t] as? Metatype)?.inhabitant ?? .error
  }

  /// Returns the type of a model witnessing the conformance of `conformer` to `concept`.
  private mutating func typeOfModel(
    of conformer: AnyTypeIdentity, conformingTo concept: TraitDeclaration.ID
  ) -> AnyTypeIdentity {
    let p = demand(Trait(declaration: concept)).erased
    let a = Value.type(conformer)
    return demand(TypeApplication(abstraction: p, arguments: [a])).erased
  }

  /// Returns the type of the implementation satisfying `requirement` in the result of `witness`.
  ///
  /// - Parameters:
  ///   - requirement: The declaration of a concept requirement.
  ///   - witness: A model witnessing a conformance to the concept defining `requirement`.
  private mutating func typeOfImplementation(
    satisfying requirement: DeclarationIdentity, in witness: WitnessExpression
  ) -> AnyTypeIdentity {
    if let d = program.cast(requirement, to: AssociatedTypeDeclaration.self) {
      return typeOfImplementation(satisfying: d, in: witness)
    } else {
      return declaredType(of: requirement, seenThrough: witness)
    }
  }

  /// Returns the type of the implementation satisfying `requirement` in the result of `witness`.
  private mutating func typeOfImplementation(
    satisfying requirement: AssociatedTypeDeclaration.ID, in witness: WitnessExpression
  ) -> AnyTypeIdentity {
    let d = program.cast(witness.declaration.target!, to: ConformanceDeclaration.self)!

    // If the declaration is abstract, just susbtitute `Self`.
    if program[d].isAbstract {
      let (_, q) = program.types.castToTraitApplication(witness.type)!
      return metatype(of: AssociatedType(declaration: requirement, qualification: q)).erased
    }

    // Otherwise, read the associated type definition.
    else if let i = implementation(of: requirement, in: d) {
      return declaredType(of: i)
    }

    // Requirement is not implemented.
    else { return .error }
  }

  /// Returns the context parameters of the type of an instance of `Self` in `s`, or `nil` if `s`
  /// isn’t notionally in the scope of a type declaration.
  private mutating func contextOfSelf(in s: ScopeIdentity) -> ContextClause? {
    guard let n = s.node else { return nil }

    switch program.tag(of: n) {
    case ConformanceDeclaration.self:
      return contextOfSelf(in: program.castUnchecked(n, to: ConformanceDeclaration.self))
    case ExtensionDeclaration.self:
      return contextOfSelf(in: program.castUnchecked(n, to: ExtensionDeclaration.self))
    case StructDeclaration.self:
      return .empty
    case TraitDeclaration.self:
      return contextOfSelf(in: program.castUnchecked(n, to: TraitDeclaration.self))
    default:
      return contextOfSelf(in: program.parent(containing: n))
    }
  }

  /// Returns the context parameters of the type of an instance of `Self` in `s`.
  private mutating func contextOfSelf(in s: ConformanceDeclaration.ID) -> ContextClause {
    let t = declaredType(of: s)
    return program.types.bodyAndContext(t).context
  }

  /// Returns the context parameters of the type of an instance of `Self` in `s`.
  private mutating func contextOfSelf(in s: ExtensionDeclaration.ID) -> ContextClause {
    let t = extendeeType(s)
    return program.types.bodyAndContext(t).context
  }

  /// Returns the context parameters of the type of an instance of `Self` in `s`.
  private mutating func contextOfSelf(in s: TraitDeclaration.ID) -> ContextClause {
    let t = demand(GenericParameter(declaration: program[s].conformer))
    let c = demand(Trait(declaration: s)).erased
    let w = demand(TypeApplication(abstraction: c, arguments: [.type(t.erased)])).erased
    return .init(parameters: [t], usings: [w])
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

  /// Returns the value of the entity referred to by `r`.
  private mutating func evaluate(_ r: DeclarationReference) -> Value {
    precondition(isStable(r), "declaration reference is not stable")
    fatalError("TODO")
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
    switch program.tag(of: d) {
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

    // Collect givens defined in `scopeOfUse`.
    var gs: [DeclarationIdentity] = []
    appendGivens(in: program.declarations(lexicallyIn: scopeOfUse), to: &gs)

    // If there aren't any givens in `scopeOfUse`, just summon in the parent scope.
    if gs.isEmpty && !scopeOfUse.isFile {
      let result = program.parent(containing: scopeOfUse).map({ (p) in summon(t, in: p) }) ?? []
      cache.scopeToSummoned[scopeOfUse, default: [:]][t] = result
      return continuation(&self, result)
    }

    // We can't just extend the set of candidates summoned in the outer scope as the introduction
    // of a new given may change the result of implicit resolution. Instead, we must consider all
    // visible givens at once.
    for p in program.scopes(from: scopeOfUse).dropFirst() {
      appendGivens(in: program.declarations(lexicallyIn: p), to: &gs)
    }
    for f in program[scopeOfUse.module].sourceFileIdentities where f != scopeOfUse.file {
      appendGivens(in: program.declarations(lexicallyIn: .init(file: f)), to: &gs)
    }
    for i in imports(of: scopeOfUse.file) {
      appendGivens(in: program[i].topLevelDeclarations, to: &gs)
    }

    let roots: [ImplicitDeduction.Continuation] = gs.map { (d) in
      let u = declaredType(of: d)
      let w = WitnessExpression(value: .reference(.direct(d)), type: u)
      return { (me) in
        me.match(w, t, in: scopeOfUse, where: subs, without: usings, withMaxDepth: maxDepth)
      }
    }

    let done = explore(roots)
    cache.scopeToSummoned[scopeOfUse, default: [:]][t] = done
    return continuation(&self, done)
  }

  /// Returns the result of implicit resolution for the roots branches.
  private mutating func explore(_ roots: [ImplicitDeduction.Continuation]) -> [SummonResult] {
    var work = roots
    var done: [SummonResult] = []

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

    return done
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

  /// Appends the declarations of compile-time givens in `ds` to `gs`.
  private func appendGivens<S: Sequence<DeclarationIdentity>>(
    in ds: S, to gs: inout [DeclarationIdentity]
  ) {
    for d in ds {
      if let g = program.cast(d, to: ConformanceDeclaration.self) { gs.append(.init(g)) }
    }
  }

  // MARK: Name resolution

  /// The context in which name resolution takes place.
  private struct TypedQualification {

    /// The expression of the qualification.
    let value: DeclarationReference.Qualification

    /// The type of the qualification.
    let type: AnyTypeIdentity

  }

  /// Resolves the declaration to which `e` refers and returns the type of `e`.
  private mutating func resolve(
    _ e: NameExpression.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let scopeOfUse = program.parent(containing: e)

    // Is the name qualified?
    if let qualification = resolveQualification(of: e, in: &context) {
      let q: TypedQualification
      if qualification.type == .error {
        return .error
      } else if qualification.type.isVariable {
        fatalError()
      } else if let t = program.types[qualification.type] as? Metatype {
        // Name resolution proceeds in the the inhabitant of the metatype rather than the metatype
        // itself so that expressions of the form `T.m` can denote entities introduced as members
        // of `T` (instead of `Metatype<T>`).
        q = .init(value: qualification.value, type: t.inhabitant)
      } else {
        q = qualification
      }

      let candidates = resolve(program[e].name.value, memberOf: q, visibleFrom: scopeOfUse)
      if candidates.isEmpty {
        let n = program[e].name
        let m = program.format("type '%T' has no member '\(n)'", [q.type])
        report(.init(.error, m, at: n.site))
        return .error
      } else {
        return assume(e, boundTo: candidates, in: &context.obligations)
      }
    }

    // Unqualified case.
    else {
      let candidates = resolve(program[e].name.value, unqualifiedIn: scopeOfUse)
      if candidates.isEmpty {
        report(program.undefinedSymbol(program[e].name))
        return .error
      } else {
        return assume(e, boundTo: candidates, in: &context.obligations)
      }
    }
  }

  /// Resolves and returns the qualification of `e`, which occurs in `context`.
  private mutating func resolveQualification(
    of e: NameExpression.ID, in context: inout InferenceContext
  ) -> TypedQualification? {
    switch program[e].qualification {
    case .none:
      return nil

    case .implicit:
      if let h = context.expectedType {
        return .init(value: .implicit, type: h)
      } else {
        report(.init(.error, "no context to resolve '\(program[e].name)'", at: program[e].site))
        return .init(value: .implicit, type: .error)
      }

    case .explicit(let p):
      let t = inferredType(of: p, in: &context)
      let u = (program.types[t] as? RemoteType)?.projectee ?? t
      return .init(value: .explicit(p), type: u)
    }
  }

  /// Returns candidates for resolving `n` without qualification in `scopeOfUse`.
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

  /// Returns candidates for resolving `n` as a member of `q` in `scopeOfUse`.
  private mutating func resolve(
    _ n: Name, memberOf q: TypedQualification, visibleFrom scopeOfUse: ScopeIdentity
  ) -> [NameResolutionCandidate] {
    var candidates: [NameResolutionCandidate] = []

    for m in declarations(nativeMembersOf: q.type)[n.identifier] ?? [] {
      let t = declaredType(of: m)
      candidates.append(.init(reference: .member(q.value, m), type: t))
    }

    candidates.append(contentsOf: resolve(n, memberInExtensionOf: q.type, visibleFrom: scopeOfUse))

    for (concept, ms) in lookup(n.identifier, memberOfTraitVisibleFrom: scopeOfUse) {
      let w = typeOfModel(of: q.type, conformingTo: concept)
      let summonings = summon(w, in: scopeOfUse)

      // TODO: report ambiguous resolution results in the candidate's diagnostics
      assert(summonings.count <= 1)

      for a in summonings {
        for m in ms {
          let w = program.types.reify(a.witness, applying: a.environment)
          let u = typeOfImplementation(satisfying: m, in: w)
          candidates.append(.init(reference: .inherited(w, m), type: u))
        }
      }
    }

    return candidates
  }

  /// Returns candidates for resolving `n` as a member in an extension of `q` in `scopeOfUse`.
  private mutating func resolve(
    _ n: Name, memberInExtensionOf q: AnyTypeIdentity, visibleFrom scopeOfUse: ScopeIdentity
  ) -> [NameResolutionCandidate] {
    // Are we in the scope of a syntax tree?
    if let p = program.parent(containing: scopeOfUse) {
      var result = resolve(n, memberInExtensionOf: q, visibleFrom: p)
      appendMatchingMembers(in: extensions(lexicallyIn: scopeOfUse), to: &result)
      return result
    }

    // We are at the top-level.
    else {
      var result: [NameResolutionCandidate] = []
      let ms = imports(of: scopeOfUse.file) + [scopeOfUse.file.module]
      for m in ms {
        appendMatchingMembers(
          in: program.collect(ExtensionDeclaration.self, in: program[m].topLevelDeclarations),
          to: &result)
      }
      return result
    }

    /// For each declaration in `es` that applies to `q`, adds to `result` the members of that
    /// declaration that are named `n`.
    func appendMatchingMembers(
      in es: [ExtensionDeclaration.ID],
      to result: inout [NameResolutionCandidate]
    ) {
      for e in es where !declarationsOnStack.contains(.init(e)) {
        if let a = applies(e, to: q, in: scopeOfUse) {
          let s = typeOfSelf(in: .init(node: e))!
          let w = program.types.reify(a.witness, applying: a.environment)

          for m in declarations(lexicallyIn: .init(node: e))[n.identifier] ?? [] {
            let member = declaredType(of: m)
            let (memberSansContext, _) = program.types.bodyAndContext(member)
            let memberAdapted = program.types.substitute(s, for: w.type, in: memberSansContext)
            result.append(.init(reference: .inherited(w, m), type: memberAdapted))
          }
        }
      }
    }
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

  /// Returns how to match a value of type `t` to apply the members of `d` in `s`.
  private mutating func applies(
    _ d: ExtensionDeclaration.ID, to t: AnyTypeIdentity, in s: ScopeIdentity
  ) -> SummonResult? {
    let u = extendeeType(d)
    let w = WitnessExpression(value: .reference(.direct(.init(d))), type: u)

    // Fast path: both types are trivially equal.
    if t == u { return .init(witness: w, environment: .init()) }

    // Slow path: use the match judgement of implicit resolution..
    let c: ImplicitDeduction.Continuation = { (me) in
      me.match(w, t, in: s, where: .init(), without: [], withMaxDepth: me.maxImplicitDepth)
    }
    return explore([c]).uniqueElement
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
      if let n = program.name(of: d) {
        m[n.identifier, default: []].append(d)
      }
    }
  }

  /// Returns the type defining the nominal scope that includes `s`, if any.
  private mutating func nominalScope(including s: ScopeIdentity) -> AnyTypeIdentity? {
    // Exit early if `s` is a file.
    guard let n = s.node else { return nil }

    // Only types have nominal scopes.
    switch program.tag(of: n) {
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
      switch program.tag(of: n) {
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

  /// Returns the identity of a fresh type variable.
  private mutating func fresh() -> TypeVariable.ID {
    program.types.fresh()
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
