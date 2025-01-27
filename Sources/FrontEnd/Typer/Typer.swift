import Algorithms
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
  private let maxImplicitDepth = 10

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

    /// The cache of `Typer.givens(atTopLevelOf:)`.
    var moduleToGivens: [[Given]?]

    /// The cache of `Typer.imports(of:in:)`.
    var sourceToImports: [[Program.ModuleIdentity]?]

    /// The cache of `Typer.extensions(lexicallyIn:)`
    var scopeToExtensions: [ScopeIdentity: [ExtensionDeclaration.ID]]

    /// The cache of `Typer.declarations(lexicallyIn:)`.
    var scopeToLookupTable: [ScopeIdentity: LookupTable]

    /// The cache of `Typer.traits(visibleFrom:)`.
    var scopeToTraits: [ScopeIdentity: [TraitDeclaration.ID]]

    /// The cache of `Typer.givens(lexicallyIn:)`.
    var scopeToGivens: [ScopeIdentity: [Given]]

    /// The cache of `Typer.summon(_:in:)`.
    var scopeToSummoned: [ScopeIdentity: [AnyTypeIdentity: [SummonResult]]]

    /// The cache of `Typer.typeOfSelf(in:)`.
    var scopeToTypeOfSelf: [ScopeIdentity: AnyTypeIdentity?]

    /// The cache of `Typer.aliasesInConformance(seenThrough:)`.
    var witnessToAliases: [WitnessExpression: [AnyTypeIdentity: AnyTypeIdentity]]

    /// The cache of `Typer.declaredType(of:)` for predefined givens.
    var predefinedGivens: [Given: AnyTypeIdentity]

    /// Creates an instance for typing `m`, which is a module in `p`.
    init(typing m: Program.ModuleIdentity, in p: Program) {
      self.moduleToIdentifierToDeclaration = .init(repeating: nil, count: p.modules.count)
      self.moduleToGivens = .init(repeating: nil, count: p.modules.count)
      self.sourceToImports = .init(repeating: nil, count: p[m].sources.count)
      self.scopeToExtensions = [:]
      self.scopeToLookupTable = [:]
      self.scopeToTraits = [:]
      self.scopeToGivens = [:]
      self.scopeToSummoned = [:]
      self.scopeToTypeOfSelf = [:]
      self.witnessToAliases = [:]
      self.predefinedGivens = [:]
    }

  }

  // MARK: Type relations

  /// Returns `true` iff `t` and `u` are equal.
  public mutating func equal(_ t: AnyTypeIdentity, _ u: AnyTypeIdentity) -> Bool {
    // Fast path: types are trivially equal.
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
    case UsingDeclaration.self:
      check(castUnchecked(d, to: UsingDeclaration.self))
    case VariableDeclaration.self:
      break
    default:
      program.unexpected(d)
    }
  }

  /// Type checks `d`.
  private mutating func check(_ d: AssociatedTypeDeclaration.ID) {
    _ = declaredType(of: d)
    // TODO: Bounds
    ensureUniqueDeclaration(d, of: program[d].identifier.value)
  }

  /// Type checks `d`.
  private mutating func check(_ d: BindingDeclaration.ID) {
    let t = declaredType(of: d)
    if let i = program[d].initializer {
      check(i, expecting: t)
    }

    program.forEachVariable(introducedBy: d) { (v, _) in
      ensureUniqueDeclaration(v, of: program[v].identifier.value)
    }
  }

  /// Type checks `d`.
  private mutating func check(_ d: ConformanceDeclaration.ID) {
    let t = declaredType(of: d)

    check(program[d].staticParameters)
    for m in program[d].members { check(m) }

    // The type of the declaration has the form `<T...> A... ==> P<B...>` where `P<B...>` is the
    // type of the declared witness and the rest forms a context. Requirements are resolved as
    // members of the type `B` where type parameters occur as skolems.
    let (witness, _) = program.types.bodyAndContext(t)
    guard let (c, conformer) = program.types.castToTraitApplication(witness) else {
      assert(t == .error)
      return
    }

    let concept = program.types[c].declaration
    var substitutions = [typeOfSelf(in: concept): conformer]

    let (requirements, associatedTypes) = program[concept].members.partitioned { (r) in
      program.tag(of: r) == AssociatedTypeDeclaration.self
    }

    // Find the implementations of associated types in the conformance declaration itself.
    for r in associatedTypes {
      let a = program.castUnchecked(r, to: AssociatedTypeDeclaration.self)
      let i = implementation(of: a, in: d).map({ (i) in declaredType(of: i) }) ?? .error

      if let m = program.types[i] as? Metatype {
        let k0 = declaredType(of: a)
        let k1 = program.types[k0] as! Metatype
        substitutions[k1.inhabitant] = m.inhabitant
      } else {
        return reportMissingImplementation(of: a)
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
        program.unexpected(r)
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
      check(program[d].staticParameters)
      check(program[d].parameters)
      check(body: program[d].body, of: .init(d), expectingOutputType: a.output)
    }

    // TODO: Redeclarations
  }

  /// Type checks `d`.
  private mutating func check(_ d: GenericParameterDeclaration.ID) {
    _ = declaredType(of: d)
    // TODO: redeclarations
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
    ensureUniqueDeclaration(d, of: program[d].identifier.value)
  }

  /// Type checks `d`.
  private mutating func check(_ d: TraitDeclaration.ID) {
    _ = declaredType(of: d)
    for m in program[d].members { check(m) }
    ensureUniqueDeclaration(d, of: program[d].identifier.value)
  }

  /// Type checks `d`.
  private mutating func check(_ d: TypeAliasDeclaration.ID) {
    _ = declaredType(of: d)
    // TODO
    ensureUniqueDeclaration(d, of: program[d].identifier.value)
  }

  /// Type checks `d`.
  private mutating func check(_ d: UsingDeclaration.ID) {
    _ = declaredType(of: d)
  }

  /// Type checks `ps`.
  private mutating func check(_ ps: [ParameterDeclaration.ID]) {
    var siblings: [String: ParameterDeclaration.ID] = .init(minimumCapacity: ps.count)
    for p in ps {
      check(p)

      // Check for duplicate parameters.
      modify(&siblings[program[p].identifier.value]) { (q) in
        if let previous = q {
          let e = program.invalidRedeclaration(
            of: .init(identifier: program[p].identifier.value),
            at: program.spanForDiagnostic(about: p),
            previousDeclarations: [program.spanForDiagnostic(about: previous)])
          report(e)
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
      return !program.isRequirement(f)
        && !program.isFFI(f) && !program.isExternal(f) && !program[f].isMemberwiseInitializer

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

  /// Returns the declarations implementing the requirement `r` of the concept `c` for the
  /// conformance of `conformer`, which is declared by `d`.
  ///
  /// The type of the implementations that may satisfy the requirement is computed by substituting
  /// the abstract types of the concept by their corresponding assignment in `subs`, and then
  /// introducing the generic parameters in the context of `conformer`, which are in `parameters`.
  private mutating func implementation(
    of r: FunctionDeclaration.ID, in c: TraitDeclaration.ID,
    for conformer: AnyTypeIdentity,
    applying subs: [AnyTypeIdentity: AnyTypeIdentity], in d: ConformanceDeclaration.ID
  ) -> DeclarationReference? {
    let requiredName = program.name(of: r)
    let requiredType = expectedImplementationType(of: r, applying: subs)
    let scopeOfUse = ScopeIdentity(node: d)
    var viable: [DeclarationReference] = []

    // Is there a unique implementation in the conformance declaration?
    for d in lookup(requiredName.identifier, lexicallyIn: .init(node: d)) {
      let candidateType = declaredType(of: d)
      if unifiable(candidateType, requiredType) { viable.append(.direct(d)) }
    }

    if let pick = viable.uniqueElement {
      return pick
    } else if !viable.isEmpty {
      reportAmbiguousImplementation(of: r, in: d)
      return nil
    }

    // Is there an implementation that is already member of the conforming type?
    let q = TypedQualification(value: .virtual, type: conformer)
    for c in resolve(requiredName, memberOf: q, visibleFrom: scopeOfUse) {
      if !unifiable(c.type, requiredType) { continue }

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

  /// Returns the expected type of an implementation of `requirement` substituting abstract types
  /// of with the assignments in `subs`.
  private mutating func expectedImplementationType(
    of requirement: FunctionDeclaration.ID, applying subs: [AnyTypeIdentity: AnyTypeIdentity]
  ) -> AnyTypeIdentity {
    let t = declaredType(of: requirement)
    return program.types.substitute(subs, in: program.types.bodyAndContext(t).body)
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

  /// Reports a diagnostic iff `d` is not the first declaration of `identifier` in its scope.
  private mutating func ensureUniqueDeclaration<T: Declaration>(_ d: T.ID, of identifier: String) {
    let p = program.parent(containing: d)
    for x in lookup(identifier, lexicallyIn: p) {
      if (x.erased != d.erased) && program.compareLexicalOccurrences(x, d) == .ascending {
        let e = program.invalidRedeclaration(
          of: .init(identifier: identifier), at: program.spanForDiagnostic(about: d),
          previousDeclarations: [program.spanForDiagnostic(about: x)])
        report(e)
        break
      }
    }
  }

  /// Type checks `e` and returns its type, which is expected to be `r` from the context of `e`.
  @discardableResult
  private mutating func check(
    _ e: ExpressionIdentity, inContextExpecting r: AnyTypeIdentity? = nil
  ) -> AnyTypeIdentity {
    if let t = program[e.module].type(assignedTo: e) {
      return t
    } else {
      var c = InferenceContext(expectedType: r)
      let t = inferredType(of: e, in: &c)
      let s = discharge(c.obligations, relatedTo: e)
      return program.types.reify(t, applying: s.substitutions)
    }
  }

  /// Type checks `e` expecting it to have type `r` and reporting an error if it doesn't.
  private mutating func check(_ e: ExpressionIdentity, expecting r: AnyTypeIdentity) {
    let u = check(e, inContextExpecting: r)

    // Fast path: `e` has the expected type or never returns.
    if equal(u, r) || equal(u, .never) { return }

    // Bail out if `e` has errors; those must have been reported already.
    if u[.hasError] { return }

    // Slow path: can we coerce `e`?
    let k = CoercionConstraint(on: e, from: u, to: r, reason: .return, at: program[e].site)
    discharge(Obligations([k]), relatedTo: e)
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
    case UsingDeclaration.self:
      return declaredType(of: castUnchecked(d, to: UsingDeclaration.self))
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

    initializeContext(program[d].staticParameters)
    let t = declaredConformanceType(program[d].extendee, program[d].concept)
    let u = introduce(program[d].staticParameters, into: t)
    program[module].setType(u, for: d)
    return u
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: FunctionDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    initializeContext(program[d].staticParameters)
    var inputs: [Parameter] = []

    // Do we have to synthesize the parameter list of a memberwise initializer?
    if program[d].introducer.value == .memberwiseinit {
      // Memberwise initializers can only appear nested in a struct declaration.
      let s = program.parent(containing: d, as: StructDeclaration.self)!
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
    }

    // Otherwise, parameters are in the syntax.
    else {
      inputs = declaredTypes(of: program[d].parameters)
    }

    let output = program[d].output.map({ (a) in evaluateTypeAscription(a) }) ?? .void
    var result: AnyTypeIdentity

    if program.isMember(d) {
      let p = program.parent(containing: d)
      let receiver = typeOfSelf(in: p)!

      var e = demand(RemoteType(projectee: receiver, access: program[d].effect.value)).erased
      e = demand(Tuple(elements: [.init(label: "self", type: e)])).erased

      result = demand(Arrow(environment: e, inputs: inputs, output: output)).erased
      result = introduce(program[d].staticParameters, into: result)
    } else {
      result = demand(Arrow(environment: .void, inputs: inputs, output: output)).erased
      result = introduce(program[d].staticParameters, into: result)
    }

    program[module].setType(result, for: d)
    return result
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: GenericParameterDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    let t = metatype(of: GenericParameter.user(d)).erased
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

    let ps = declaredTypes(of: program[d].staticParameters.explicit)
    if let i = program[d].staticParameters.implicit.first {
      let s = program.spanForDiagnostic(about: i)
      report(.init(.error, "context parameters in type definitions are not supported yet", at: s))
    }

    if ps.isEmpty {
      let t = metatype(of: Struct(declaration: d)).erased
      program[module].setType(t, for: d)
      return t
    } else {
      let a = TypeApplication.Arguments(uniqueKeysWithValues: ps.map({ (p) in (p, p.erased) }))
      let f = demand(Struct(declaration: d)).erased
      let t = metatype(of: TypeApplication(abstraction: f, arguments: a)).erased
      let u = demand(UniversalType(parameters: ps, body: t)).erased
      program[module].setType(u, for: d)
      return u
    }
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

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: UsingDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[d.module].type(assignedTo: d) { return memoized }
    assert(d.module == module, "dependency is not typed")

    let t: AnyTypeIdentity
    switch program[d].semantics.value {
    case .conformance:
      t = declaredConformanceType(program[d].lhs, program[d].rhs)
    case .equality:
      t = declaredEqualityType(program[d].lhs, program[d].rhs)
    }
    program[module].setType(t, for: d)
    return t
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

  /// Returns the declared types of `ps` without checking.
  private mutating func declaredTypes(
    of ps: [GenericParameterDeclaration.ID]
  ) -> [GenericParameter.ID] {
    ps.compactMap { (p) in
      let t = declaredType(of: p)
      return program.types
        .select(\Metatype.inhabitant, on: t)
        .flatMap({ (m) in program.types.cast(m, to: GenericParameter.self) })
    }
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
    else if let concept = program.types[c] as? Trait {
      return typeOfModel(of: e, conformingTo: concept.declaration)
    }

    // Is the expression of the concept denoting something other than a trait?
    else {
      let m = program.format("'%T' is not a trait", [c])
      let s = program[concept].site
      report(.init(.error, m, at: s))
      return .error
    }
  }

  /// Returns the type of a value witnessing the conformance of `lhs` to `rhs`.
  private mutating func declaredEqualityType(
    _ lhs: ExpressionIdentity, _ rhs: ExpressionIdentity
  ) -> AnyTypeIdentity {
    let l = evaluateTypeAscription(lhs)
    let r = evaluateTypeAscription(rhs)

    // Was there an error?
    if (l == .error) || (r == .error) {
      return .error
    }

    // All is well.
    else {
      return demand(EqualityWitness(lhs: l, rhs: r)).erased
    }
  }

  /// Returns the declared type of `g` without checking.
  private mutating func declaredType(of g: Given) -> AnyTypeIdentity {
    if case .user(let d) = g {
      return declaredType(of: d)
    } else if case .assumed(_, let t) = g {
      return t
    } else if let t = cache.predefinedGivens[g] {
      return t
    }

    let result: AnyTypeIdentity
    switch g {
    case .coercion(.reflexivity):
      // <T> T ~ T
      let t0 = demand(GenericParameter.reflexivity)
      let x0 = demand(EqualityWitness(lhs: t0.erased, rhs: t0.erased)).erased
      result = demand(UniversalType(parameters: [t0], body: x0)).erased

    case .coercion(.symmetry):
      // <T0, T1> T0 ~ T1 ==> T1 ~ T0
      let t0 = demand(GenericParameter.symmetry(0))
      let t1 = demand(GenericParameter.symmetry(1))
      let x0 = demand(EqualityWitness(lhs: t0.erased, rhs: t1.erased)).erased
      let x1 = demand(EqualityWitness(lhs: t1.erased, rhs: t0.erased)).erased
      let x2 = demand(Implication(context: [x0], head: x1)).erased
      result = demand(UniversalType(parameters: [t0, t1], body: x2)).erased

    case .coercion(.transitivity):
      // <T0, T1, T2> T0 ~ T1, T1 ~ T2 ==> T0 ~ T2
      let t0 = demand(GenericParameter.transitivity(0))
      let t1 = demand(GenericParameter.transitivity(1))
      let t2 = demand(GenericParameter.transitivity(2))
      let x0 = demand(EqualityWitness(lhs: t0.erased, rhs: t1.erased)).erased
      let x1 = demand(EqualityWitness(lhs: t1.erased, rhs: t2.erased)).erased
      let x2 = demand(EqualityWitness(lhs: t0.erased, rhs: t2.erased)).erased
      let x3 = demand(Implication(context: [x0, x1], head: x2)).erased
      result = demand(UniversalType(parameters: [t0, t1, t2], body: x3)).erased

    case .assumed, .user:
      unreachable()
    }

    cache.predefinedGivens[g] = result
    return result
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

    initializeContext(program[d].staticParameters)
    let t = ignoring(d, { (me) in me.evaluateTypeAscription(me.program[d].extendee) })
    let u = introduce(program[d].staticParameters, into: t)
    program[module].setType(u, for: d)
    return u
  }

  /// Computes the types of the given context parameters, introducing them in order.
  private mutating func initializeContext(_ parameters: StaticParameters) {
    declarationsOnStack.formUnion(parameters.implicit)
    for p in parameters.implicit {
      _ = declaredType(of: p)
      let q = declarationsOnStack.remove(p)
      assert(q != nil)
    }
  }

  /// Returns `t` as the head of a universal type and/or implication introducing `parameters`.
  private mutating func introduce(
    _ parameters: StaticParameters, into t: AnyTypeIdentity
  ) -> AnyTypeIdentity {
    if parameters.isEmpty { return t }

    let ps = declaredTypes(of: parameters.explicit)
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
    case Conversion.self:
      return inferredType(of: castUnchecked(e, to: Conversion.self), in: &context)
    case NameExpression.self:
      return inferredType(of: castUnchecked(e, to: NameExpression.self), in: &context)
    case New.self:
      return inferredType(of: castUnchecked(e, to: New.self), in: &context)
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
    let callee = program[e].callee
    let r = SyntaxRole(program[e].style, labels: program[e].labels)
    let f = context.withSubcontext(role: r) { (ctx) in
      inferredType(of: callee, in: &ctx)
    }

    // Is the callee referring to a sugared constructor?
    if isTypeDeclarationReference(callee) {
      let site = program[callee].site
      let n = program[module].insert(
        NameExpression(qualification: callee, name: .init("new", at: site), site: site),
        in: program.parent(containing: e))
      program[module].replace(.init(e), for: program[e].replacing(callee: .init(n)))
      return context.withSubcontext(role: r) { (ctx) in
        inferredType(of: n, in: &ctx)
      }
    }

    // Otherwise, returns the inferred type as-is.
    else { return f }

    /// Returns `true` iff `e` is a type declaration reference.
    ///
    /// `e` is a type declaration reference if it is a name expression bound to a metatype or if it
    /// is the static application of a type declaration reference.
    ///
    /// - Requires: The types of `e` and its children have been assigned in `context`.
    func isTypeDeclarationReference(_ e: ExpressionIdentity) -> Bool {
      if program.tag(of: e) == NameExpression.self {
        let head = program.types.head(context.obligations.syntaxToType[e.erased]!)
        return program.types.tag(of: head) == Metatype.self
      } else if let n = program.cast(e, to: StaticCall.self) {
        return isTypeDeclarationReference(program[n].callee)
      } else {
        return false
      }
    }
  }

  /// Returns the inferred type of `e`'s callee.
  private mutating func inferredType(
    of e: Conversion.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let h = context.expectedType.map({ (m) in demand(Metatype(inhabitant: m)).erased })
    let target = context.withSubcontext(expectedType: h) { (ctx) in
      inferredType(of: program[e].target, in: &ctx)
    }

    // The right-hand side denotes a type?
    if let rhs = (program.types[target] as? Metatype)?.inhabitant {
      // The right-hand side injects an expected type for the left-hand side.
      let lhs = context.withSubcontext(expectedType: rhs) { (ctx) in
        inferredType(of: program[e].source, in: &ctx)
      }

      switch program[e].semantics {
      case .up:
        let s = program.spanForDiagnostic(about: program[e].source)
        context.obligations.assume(WideningConstraint(lhs: lhs, rhs: rhs, site: s))
      case .down:
        let s = program.spanForDiagnostic(about: program[e].target)
        context.obligations.assume(WideningConstraint(lhs: rhs, rhs: lhs, site: s))
      case .pointer:
        if program.types.tag(of: rhs) != RemoteType.self {
          fatalError()
        }
      }

      return context.obligations.assume(e, hasType: rhs, at: program[e].site)
    }

    // Inference failed on the right-hand side.
    else if target == .error {
      // Error already reported.
      return context.obligations.assume(e, hasType: .error, at: program[e].site)
    } else {
      report(program.doesNotDenoteType(program[e].target))
      return context.obligations.assume(e, hasType: .error, at: program[e].site)
    }
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: NameExpression.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let s = program.spanForDiagnostic(about: e)

    // Is `e` a constructor reference?
    if program.isConstructorReference(e) {
      let n = program[module].insert(
        NameExpression(qualification: nil, name: .init("init", at: s), site: s),
        in: program.parent(containing: e))
      let m = program[module].replace(
        .init(e),
        for: New(qualification: program[e].qualification!, target: n, site: program[e].site))
      return inferredType(of: m, in: &context)
    }

    // Otherwise, proceed as usual.
    else {
      let t = resolve(e, in: &context)
      return context.obligations.assume(e, hasType: t, at: s)
    }
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: New.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let site = program.spanForDiagnostic(about: e)

    let t = resolveQualification(of: e, in: &context)
    let u = fresh().erased
    let q = TypedQualification(value: .virtual, type: t)
    context.obligations.assume(
      MemberConstraint(
        member: program[e].target, role: context.role, qualification: q, type: u, site: site))
    context.obligations.assume(program[e].target, hasType: u, at: site)

    let v = context.expectedType ?? fresh().erased
    context.obligations.assume(ConstructorConversionConstraint(lhs: u, rhs: v, site: site))
    return context.obligations.assume(e, hasType: v, at: site)
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
    if let computed =  context.obligations.syntaxToType[e.erased] { return computed }

    // Abstraction is inferred in the same inference context.
    guard let f = inferredType(of: program[e].callee, in: &context).unlessError else {
      return context.obligations.assume(e, hasType: .error, at: program[e].site)
    }

    let i = program[e].arguments.map { (a) in
      evaluatePartialTypeAscription(a, in: &context).result
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

    // Slow path: infer a type from the ascription and (if necessary) the initializer.
    let (p, isPartial) = evaluatePartialTypeAscription(a, in: &context)
    if isPartial, let i = program[d].initializer {
      let v = context.withSubcontext(expectedType: p, do: { (s) in inferredType(of: i, in: &s) })
      if v != .error {
        context.obligations.assume(CoercionConstraint(on: i, from: v, to: p, at: program[i].site))
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

  /// Binds `n` to candidates in `cs` suitable for the given `role` and returns the inferred type
  /// of `n`, or a diagnostic reported at `site` if `cs` contains no viable candidate.
  ///
  /// If binding succeeds, `o` is extended with either a assignment mapping `n` to a declaration
  /// reference or an overload constrain mapping `n` to one of the viable candidates. If binding
  /// failed, `o` is left unchanged and a diagnostic is returned.
  ///
  /// - Requires: `cs` is not empty.
  internal mutating func assume(
    _ n: NameExpression.ID, boundTo cs: consuming [NameResolutionCandidate],
    for role: SyntaxRole, at site: SourceSpan, in o: inout Obligations
  ) -> Either<AnyTypeIdentity, Diagnostic> {
    assert(!cs.isEmpty)

    // No candidate survived filtering?
    if let d = filter(&cs, for: role, at: site) {
      return .right(d)
    }

    // There is only one candidate left?
    else if cs.count == 1 {
      o.assume(n, boundTo: cs[0].reference)
      return .left(cs[0].type)
    }

    // Otherwise, create an overload set.
    else {
      let t = fresh().erased
      o.assume(OverloadConstraint(name: n, type: t, candidates: cs, site: site))
      return .left(t)
    }
  }

  /// Narrows the overloaded candidates in `cs` to keep those suitable for the given `role`,
  /// returning a diagnostic iff no candidate survived.
  ///
  /// - Note: No filtering is applied if `cs` contains less than two elements.
  private func filter(
    _ cs: inout [NameResolutionCandidate], for role: SyntaxRole, at site: SourceSpan
  ) -> Diagnostic? {
    switch role {
    case _ where cs.count <= 1:
      return nil
    case .ascription, .unspecified:
      return nil
    case .function(let labels):
      return filter(&cs, callable: .parenthesized, withLabels: labels, at: site)
    case .subscript(let labels):
      return filter(&cs, callable: .bracketed, withLabels: labels, at: site)
    }
  }

  /// Narrows the overloaded candidates in `cs` to keep those that can be applied with the given
  /// style and argument labels, returning a diagnostic iff no candidate survived.
  ///
  /// - Requires: `cs` is not empty.
  private func filter(
    _ cs: inout [NameResolutionCandidate],
    callable style: Call.Style, withLabels labels: [String?], at site: SourceSpan
  ) -> Diagnostic? {
    // Non-viable candidates moved at the end.
    let i = cs.stablePartition { (c) in
      !program.types.isCallable(headOf: c.type, style, withLabels: labels)
    }
    defer { cs.removeSubrange(i...) }

    if i != 0 {
      return nil
    } else {
      // Only candidates having a declaration in source are added to the notes. Other candidates
      // are not overloadable and so we can assume that another error will be diagnosed.
      let notes = cs.compactMap { (c) -> Diagnostic? in
        guard let d = c.reference.target else { return nil }
        let s = program.spanForDiagnostic(about: d)
        let h = program.types.head(c.type)

        if let t = program.types[h] as? any Callable, t.style == style {
          return program.incompatibleLabels(found: t.labels, expected: labels, at: s, as: .note)
        } else {
          return .init(.note, "candidate not viable", at: s)
        }
      }
      return .init(.error, "no candidate matches the argument list", at: site, notes: notes)
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

  /// Stores the assignments made in `s` to solve `o` into the program.
  private mutating func commit(_ s: Solution, to o: Obligations) {
    for d in s.diagnostics.elements { report(d) }

    // Incomplete inference results are diagnosed only once and only if no other diagnostic was
    // reported by the solver.
    var inferenceFailureDiagnosed = s.diagnostics.containsError
    for (n, t) in o.syntaxToType {
      var u = program.types.reify(t, applying: s.substitutions, withVariables: .kept)
      if u[.hasVariable] {
        u = program.types.substituteVariableForError(in: u)
        if !inferenceFailureDiagnosed {
          report(program.notEnoughContext(n))
          inferenceFailureDiagnosed = true
        }
      }
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
    return (program.types[program.types.head(t)] as? Metatype)?.inhabitant ?? .error
  }

  /// Returns the type of an instance of `Self` in `s`.
  private mutating func typeOfSelf(in d: TraitDeclaration.ID) -> AnyTypeIdentity {
    let t = declaredType(of: program[d].conformer)
    return (program.types[program.types.head(t)] as? Metatype)?.inhabitant ?? .error
  }

  /// Returns the type of a model witnessing the conformance of `conformer` to `concept`.
  private mutating func typeOfModel(
    of conformer: AnyTypeIdentity, conformingTo concept: TraitDeclaration.ID
  ) -> AnyTypeIdentity {
    let f = demand(Trait(declaration: concept)).erased
    let p = demand(GenericParameter.user(program[concept].conformer))
    return demand(TypeApplication(abstraction: f, arguments: [p: conformer])).erased
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
    assert(program.types.castToTraitApplication(witness.type) != nil)

    // The witness is the result of a coercion?
    if let (_, b) = asCoercionApplication(witness) {
      return typeOfImplementation(satisfying: requirement, in: b)
    }

    // The witness refers to a given declaration?
    else if let d = witness.declaration, let c = program.cast(d, to: ConformanceDeclaration.self) {
      // Read the associated type definition.
      if let i = implementation(of: requirement, in: c) {
        return declaredType(of: i)
      } else {
        return .error
      }
    }

    // Otherwise, the value of the witness is opaque.
    else {
      let (_, q) = program.types.castToTraitApplication(witness.type)!
      return metatype(of: AssociatedType(declaration: requirement, qualification: q)).erased
    }
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
    let p = demand(GenericParameter.user(program[s].conformer))
    let w = typeOfModel(of: p.erased, conformingTo: s)
    return .init(parameters: [p], usings: [w])
  }

  // MARK: Compile-time evaluation

  /// Returns the value of `e` evaluated as a type ascription.
  private mutating func evaluateTypeAscription(_ e: ExpressionIdentity) -> AnyTypeIdentity {
    var c = InferenceContext()
    let (t, _) = evaluatePartialTypeAscription(e, in: &c)
    let s = discharge(c.obligations, relatedTo: e)
    return program.types.reify(t, applying: s.substitutions)
  }

  /// Returns the value of `e` evaluated as a (possibly partial) type ascription.
  private mutating func evaluatePartialTypeAscription(
    _ e: ExpressionIdentity, in context: inout InferenceContext
  ) -> (result: AnyTypeIdentity, isPartial: Bool) {
    let t = context.withSubcontext(role: .ascription) { (ctx) in
      inferredType(of: e, in: &ctx)
    }

    let h = inhabitant(of: t, coercingIfNecessary: e, in: &context)
    return (result: h, isPartial: t[.hasVariable])
  }

  /// Returns the inhabitant of `t`, which is the type of the ascription `e`.
  private mutating func inhabitant(
    of t: AnyTypeIdentity, coercingIfNecessary e: ExpressionIdentity,
    in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    if t == .error {
      return .error
    } else if let m = program.types[t] as? Metatype {
      return m.inhabitant
    } else {
      let h = fresh().erased
      let u = demand(Metatype(inhabitant: h)).erased
      context.obligations.assume(
        CoercionConstraint(on: e, from: t, to: u, reason: .ascription, at: program[e].site))
      return h
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

  /// A witness resolved by implicit resolution.
  internal struct SummonResult {

    /// The expression of the witness.
    internal let witness: WitnessExpression

    /// A table assigning the open variables of the witness's type.
    internal let substitutions: SubstitutionTable

  }

  /// The process of elaborating a the value of a witness satisfying having some given type.
  ///
  /// An instance represents a possibly non-terminating thread of execution modeling the steps of a
  /// witness' resolution. Taking a step yields either a witness (when resolution completes) or a
  /// set of other threads representing all possible conclusions.
  private struct ResolutionThread {

    /// The result of taking a step in a resolution thread.
    enum Advanced {

      /// The thread has completed execution.
      case done(SummonResult)

      /// The thread has taken a step and suspended, spawning zero or threads to resume.
      case next([ResolutionThread])

    }

    /// A part of a thread continuation.
    enum ContinuationItem {

      /// Either the result of a thread or an operand to a thread continuation.
      case done(SummonResult)

      /// A continuation substituting assumed witnesses of the given type by a summoned witness.
      case substitute(Int)

    }

    /// The environment of a thread, representing open variable assignments and assumed givens.
    struct Environment {

      /// A table from open variable to its assignment.
      let substitutions: SubstitutionTable

      /// The set of assumed givens.
      let givens: [Given]

      /// The identifier of the next assumed given.
      let nextGivenIdentifier: Int

      /// Returns a copy of `self` in which `ts` are assumed given.
      func assuming(givens ts: [AnyTypeIdentity]) -> Environment {
        let gs = ts.enumerated().map({ (i, t) in Given.assumed(nextGivenIdentifier + i, t) })
        let e = Environment(
          substitutions: substitutions, givens: givens + gs,
          nextGivenIdentifier: nextGivenIdentifier + gs.count)
        return e
      }

      func assuming(given t: AnyTypeIdentity) -> (Environment, WitnessExpression) {
        let i = nextGivenIdentifier
        let g = Given.assumed(i, t)
        let e = Environment(
          substitutions: substitutions, givens: givens + [g], nextGivenIdentifier: i + 1)
        return (e, .init(value: .reference(.assumed(i, t)), type: t))
      }

      /// An empty environment.
      static var empty: Environment {
        .init(substitutions: .init(), givens: [], nextGivenIdentifier: 0)
      }

    }

    /// The witness being resolved, whose value is matched against some queried type.
    let witness: WitnessExpression

    /// The type of the witness to resolve.
    let queried: AnyTypeIdentity

    /// The environment in which matching takes place.
    let environment: Environment

    /// The thread's continuation.
    ///
    /// A continuation is represented as a stack of operands and operators, encoding an operation
    /// in a tack-based DSL.
    let tail: [ContinuationItem]

  }

  /// Returns witnesses of values of type `t` derivable from the implicit store in `scopeOfUse`.
  internal mutating func summon(
    _ t: AnyTypeIdentity, in scopeOfUse: ScopeIdentity
  ) -> [SummonResult] {
    // Did we already compute the result?
    if let table = cache.scopeToSummoned[scopeOfUse], let result = table[t] {
      return result
    }

    let result: [SummonResult]

    // If there aren't any givens in `scopeOfUse`, just summon in the parent scope.
    if givens(lexicallyIn: scopeOfUse).isEmpty, let p = program.parent(containing: scopeOfUse) {
      result = summon(t, in: p)
    }

    // Otherwise, we can't just extend the set of candidates summoned in the outer scope as the
    // introduction of a new given may change the result of implicit resolution. Instead, we must
    // consider all visible givens at once.
    else {
      let threads = summon(t, in: scopeOfUse, where: .empty, then: [])
      result = takeSummonResults(from: threads, in: scopeOfUse)
    }

    cache.scopeToSummoned[scopeOfUse, default: [:]][t] = result
    return result
  }

  /// Returns the result of `continuation` applied to witnesses of values of type `t` derivable
  /// from the implicit store in `scopeOfUse`.
  ///
  /// - Parameters:
  ///   - t: The type whose instance is summoned.
  ///   - scopeOfUse: The scope in which the witnesses are resolve.
  ///   - environment: An assignment of unification variables in `t` and a set of assumed givens.
  ///   - continuation: The work to be done with the summoned results.
  private mutating func summon(
    _ t: AnyTypeIdentity, in scopeOfUse: ScopeIdentity,
    where environment: ResolutionThread.Environment,
    then continuation: [ResolutionThread.ContinuationItem]
  ) -> [ResolutionThread] {
    var gs: [Given] = []

    // Givens visible from `scopeOfUse`.
    for s in program.scopes(from: scopeOfUse) {
      for g in givens(lexicallyIn: s) where !isOnStack(g) { gs.append(g) }
    }
    for f in program[scopeOfUse.module].sourceFileIdentities where f != scopeOfUse.file {
      for g in givens(lexicallyIn: .init(file: f)) where !isOnStack(g) { gs.append(g) }
    }
    for i in imports(of: scopeOfUse.file) {
      for g in givens(atTopLevelOf: i) where !isOnStack(g) { gs.append(g) }
    }

    // Assumed givens.
    gs.append(contentsOf: environment.givens)

    // Built-in givens.
    gs.append(.coercion(.reflexivity))
    gs.append(.coercion(.symmetry))
    gs.append(.coercion(.transitivity))

    return gs.map { (g) -> ResolutionThread in
      let u = declaredType(of: g)
      let v: WitnessExpression.Value
      switch g {
      case .user(let d):
        v = .reference(.direct(d))
      case .coercion:
        v = .reference(.builtin(.coercion))
      case .assumed(let i, let t):
        v = .reference(.assumed(i, t))
      }
      let w = WitnessExpression(value: v, type: u)
      return .init(witness: w, queried: t, environment: environment, tail: continuation)
    }
  }

  /// Returns the result of taking a step in `thread`, which resolves a witness in `scopeOfUse`.
  private mutating func match(
    _ thread: ResolutionThread, in scopeOfUse: ScopeIdentity
  ) -> ResolutionThread.Advanced {
    // Weak-head normal forms.
    let a = program.types.reify(
      thread.witness.type, applying: thread.environment.substitutions, withVariables: .kept)
    let b = program.types.reify(
      thread.queried, applying: thread.environment.substitutions, withVariables: .kept)

    // The witness has a universal type?
    if let u = program.types[a] as? UniversalType {
      var vs = TypeApplication.Arguments(minimumCapacity: u.parameters.count)
      for p in u.parameters {
        vs[p] = fresh().erased
      }

      let w = WitnessExpression(
        value: .typeApplication(thread.witness, vs),
        type: program.types.substitute(vs, in: u.body))
      return .next([
        .init(witness: w, queried: b, environment: thread.environment, tail: thread.tail)
      ])
    }

    // The witness is an implication?
    else if let i = program.types[a] as? Implication {
      // Assume that the implication has a non-empty context.
      let h = i.context.first!
      let (e, v) = thread.environment.assuming(given: h)
      let w = WitnessExpression(
        value: .termApplication(thread.witness, v),
        type: program.types.dropFirstRequirement(.init(uncheckedFrom: a)))
      return .next([
        .init(witness: w, queried: b, environment: e, tail: thread.tail)
      ])
    }

    // The witness has a simple type; attempt a match.
    var subs = SubstitutionTable()
    var coercions: [(AnyTypeIdentity, AnyTypeIdentity)] = []
    _ = program.types.unifiable(a, b, extending: &subs) { (x, y) in
      coercions.append((x, y))
      return true
    }

    // No coercion required?
    if coercions.isEmpty {
      let s = thread.environment.substitutions.union(subs)
      let w = program.types.reify(thread.witness, applying: s, withVariables: .kept)
      if w.type[.hasError] { return .next([]) }
      assert(!w.type[.hasError])
      let r = SummonResult(witness: w, substitutions: s)
      return threadContinuation(appending: r, to: thread, in: scopeOfUse)
    }

    // Resolution failed if nothing matches structurally.
    else if let (x, y) = coercions.uniqueElement, (x == a), (y == b) {
      return .next([])
    }

    // Properties of equality are encoded as axioms so there is no need to assume non-syntactic
    // equalities between parts of equality witnesses.
    else if program.types.isEquality(a) || program.types.isEquality(b) {
      return .next([])
    }

    // Otherwise, assume non-syntactic equalities between pairwise parts.
    let e = thread.environment.assuming(
      givens: coercions.map({ (c) in demand(EqualityWitness(lhs: c.0, rhs: c.1)).erased }))
    let t = demand(EqualityWitness(lhs: a, rhs: b)).erased
    let w = WitnessExpression(
      value: .termApplication(.init(builtin: .coercion, type: t), thread.witness),
      type: b)
    return .next([
      .init(witness: w, queried: b, environment: e, tail: thread.tail)
    ])
  }

  /// Returns the continuation of `thread` after having resolved `operand` in `scopeOfUse`.
  private mutating func threadContinuation(
    appending operand: SummonResult, to thread: ResolutionThread, in scopeOfUse: ScopeIdentity
  ) -> ResolutionThread.Advanced {
    // Are there assumptions to discharge?
    if case .assumed(let i, let assumed) = thread.environment.givens.last {
      let e = ResolutionThread.Environment(
        substitutions: operand.substitutions, givens: thread.environment.givens.dropLast(),
        nextGivenIdentifier: thread.environment.nextGivenIdentifier)
      var t = thread.tail
      t.append(.done(operand))
      t.append(.substitute(i))
      return .next(summon(assumed, in: scopeOfUse, where: e, then: t))
    }

    // We're done; apply the continuation.
    else {
      assert(thread.environment.givens.isEmpty)
      return .done(applyContinuation(thread.tail[...], to: operand))
    }
  }

  /// Returns the result of  `continuation` applied to `operand`.
  private mutating func applyContinuation(
    _ continuation: ArraySlice<ResolutionThread.ContinuationItem>, to operand: SummonResult
  ) -> SummonResult {
    switch continuation.last {
    case .some(.substitute(let i)):
      let r = executeContinuation(continuation.dropLast())
      let x = r.witness.substituting(assumed: i, for: operand.witness.value)
      let e = operand.substitutions.union(r.substitutions)
      return .init(
        witness: program.types.reify(x, applying: e, withVariables: .kept), substitutions: e)

    case .some(.done):
      unreachable("ill-formed continuation")

    case .none:
      let w = program.types.reify(
        operand.witness, applying: operand.substitutions, withVariables: .kept)
      return .init(witness: w, substitutions: operand.substitutions)
    }
  }

  /// Returns the result of the given thread continuation.
  private mutating func executeContinuation(
    _ continuation: ArraySlice<ResolutionThread.ContinuationItem>
  ) -> SummonResult {
    if case .some(.done(let a)) = continuation.last {
      applyContinuation(continuation.dropLast(), to: a)
    } else {
      unreachable("ill-formed continuation")
    }
  }

  /// Returns the results of `threads`, which are defined in `scopeOfUse`.
  private mutating func takeSummonResults(
    from threads: [ResolutionThread], in scopeOfUse: ScopeIdentity
  ) -> [SummonResult] {
    var work = threads
    var done: [SummonResult] = []
    var depth = 0

    while done.isEmpty && !work.isEmpty && (depth < maxImplicitDepth) {
      var next: [ResolutionThread] = []
      for item in work {
        switch match(item, in: scopeOfUse) {
        case .done(let r): done.append(r)
        case .next(let s): next.append(contentsOf: s)
        }
      }
      depth += 1
      swap(&next, &work)
    }

    return done
  }

  /// Returns the givens whose definitions are at the top-level of `m`.
  private mutating func givens(atTopLevelOf m: Program.ModuleIdentity) -> [Given] {
    if let memoized = cache.moduleToGivens[m] { return memoized }

    var gs: [Given] = []
    appendGivens(in: program[m].topLevelDeclarations, to: &gs)
    cache.moduleToGivens[m] = gs
    return gs
  }

  /// Returns the givens whose definitions are directly contained in `s`.
  private mutating func givens(lexicallyIn s: ScopeIdentity) -> [Given] {
    if let memoized = cache.scopeToGivens[s] { return memoized }

    var gs: [Given] = []
    appendGivens(in: program.declarations(lexicallyIn: s), to: &gs)
    cache.scopeToGivens[s] = gs
    return gs
  }

  /// Appends the declarations of compile-time givens in `ds` to `gs`.
  private func appendGivens<S: Sequence<DeclarationIdentity>>(in ds: S, to gs: inout [Given]) {
    for d in ds {
      switch program.tag(of: d) {
      case ConformanceDeclaration.self, UsingDeclaration.self:
        gs.append(.user(d))
      default:
        continue
      }
    }
  }

  /// Returns the possible ways to elaborate `e`, which has type `a`, as an expression of type `b`.
  internal mutating func coerced(
    _ e: ExpressionIdentity, withType a: AnyTypeIdentity, toMatch b: AnyTypeIdentity
  ) -> [SummonResult] {
    // Fast path: types are unifiable without any coercion.
    if let subs = program.types.unifiable(a, b) {
      return [SummonResult(witness: .init(value: .identity(e), type: a), substitutions: subs)]
    }

    // Slow path: compute an elaboration.
    var main = ResolutionThread(
      witness: .init(value: .identity(e), type: a), queried: b, environment: .empty, tail: [])

    // Apply the rules of the matching judgement until we get a simple type. For example, if `a`
    // is a universal type `<T> X ==> A<T>`, we want a witness of type `A<%0>` in an environment
    // where `%0` is a unification variable and `X` is assumed.
    let scopeOfUse = program.parent(containing: e)
    while program.types.hasContext(main.witness.type) {
      switch match(main, in: scopeOfUse) {
      case .next(let s): main = s.uniqueElement!
      case .done: unreachable()
      }
    }

    // Either the type of the elaborated witness is unifiable with the queried type or we need to
    // assume a coercion. Implicit resolution will figure out the "cheapest" alternative.
    let (e, f) = main.environment.assuming(
      given: demand(EqualityWitness(lhs: main.witness.type, rhs: b)).erased)
    let w = WitnessExpression(value: .termApplication(f, main.witness), type: b)
    let withCoercion = ResolutionThread(witness: w, queried: b, environment: e, tail: main.tail)
    return takeSummonResults(from: [main, withCoercion], in: scopeOfUse)
  }

  // MARK: Name resolution

  /// Resolves the declaration to which `e` refers and returns the type of `e`.
  private mutating func resolve(
    _ e: NameExpression.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let scopeOfUse = program.parent(containing: e)
    let site = program.spanForDiagnostic(about: e)
    let cs: [NameResolutionCandidate]

    // Is the name qualified?
    if let q = resolveQualification(of: e, in: &context) {
      if q.type.isVariable {
        let t = context.expectedType ?? fresh().erased
        let k = MemberConstraint(
          member: e, role: context.role, qualification: q, type: t, site: site)
        context.obligations.assume(k)
        return context.obligations.assume(e, hasType: t, at: site)
      } else if q.type == .error {
        return context.obligations.assume(e, hasType: .error, at: site)
      }

      cs = resolve(program[e].name.value, memberOf: q, visibleFrom: scopeOfUse)
      if cs.isEmpty {
        report(program.undefinedSymbol(program[e].name, memberOf: q.type))
        return context.obligations.assume(e, hasType: .error, at: site)
      }
    }

    // Unqualified case.
    else {
      cs = resolve(program[e].name.value, unqualifiedIn: scopeOfUse)
      if cs.isEmpty {
        report(program.undefinedSymbol(program[e].name))
        return context.obligations.assume(e, hasType: .error, at: site)
      }
    }

    switch assume(e, boundTo: cs, for: context.role, at: site, in: &context.obligations) {
    case .left(let t):
      return t
    case .right(let d):
      report(d)
      return .error
    }
  }

  /// Resolves and returns the qualification of `e`, which occurs in `context`.
  private mutating func resolveQualification(
    of e: NameExpression.ID, in context: inout InferenceContext
  ) -> TypedQualification? {
    // No qualification?
    guard let q = program[e].qualification else { return nil }

    if program.tag(of: q) == ImplicitQualification.self {
      if let t = context.expectedType {
        context.obligations.assume(q, hasType: t, at: program[q].site)
        return qualificationForSelectionOn(.explicit(q), withType: t)
      } else {
        let n = program[e].name
        report(.init(.error, "no context to resolve '\(n)'", at: n.site))
        return .init(value: .explicit(q), type: .error)
      }
    } else {
      let t = inferredType(of: q, in: &context)
      return qualificationForSelectionOn(.explicit(q), withType: t)
    }
  }

  /// Resolves and returns the qualification of `e`, which occurs in `context`.
  private mutating func resolveQualification(
    of e: New.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let q = program[e].qualification

    if program.tag(of: q) == ImplicitQualification.self {
      if let t = context.expectedType {
        context.obligations.assume(q, hasType: t, at: program[q].site)
        return t
      } else {
        let s = program.spanForDiagnostic(about: e)
        report(.init(.error, "no context to resolve constructor reference", at: s))
        return .error
      }
    } else {
      return evaluatePartialTypeAscription(q, in: &context).result
    }
  }

  /// Returns the type in which qualified name lookup should be performed to select a member on a
  /// qualification `q` of type `t`.
  internal mutating func qualificationForSelectionOn(
    _ q: DeclarationReference.Qualification, withType t: AnyTypeIdentity
  ) -> TypedQualification {
    // If the qualification has a remote type, name resolution proceeds with the projectee.
    if let u = program.types[t] as? RemoteType {
      return .init(value: q, type: u.projectee)
    }

    // If the qualification has a metatype, name resolution proceeds with the inhabitant so that
    // expressions of the form `T.m` can denote entities introduced as members of `T` (rather
    // than `Metatype<T>`). If context clause of the qualification is preserved to support member
    // selection on unapplied type constructors (e.g., `Array.new`).
    let (body, context) = program.types.bodyAndContext(t)
    if let m = program.types[body] as? Metatype {
      let u = program.types.introduce(context, into: m.inhabitant)
      return .init(value: q, type: u)
    } else {
      return .init(value: q, type: t)
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
        return [.init(reference: .builtin(.alias), type: u)]
      } else {
        return []
      }

    case "self":
      if let t = typeOfSelf(in: scopeOfUse) {
        return [.init(reference: .builtin(.alias), type: t)]
      } else {
        return []
      }

    case "Never":
      let t = demand(Metatype(inhabitant: .never)).erased
      return [.init(reference: .builtin(.alias), type: t)]

    case "Void":
      let t = demand(Metatype(inhabitant: .void)).erased
      return [.init(reference: .builtin(.alias), type: t)]

    default:
      return []
    }
  }

  /// Returns candidates for resolving `n` as a member of `q` in `scopeOfUse`.
  ///
  /// - Requires: `q.type` is not a unification variable.
  internal mutating func resolve(
    _ n: Name, memberOf q: TypedQualification, visibleFrom scopeOfUse: ScopeIdentity
  ) -> [NameResolutionCandidate] {
    var candidates = resolve(n, nativeMemberOf: q)

    candidates.append(contentsOf: resolve(n, memberInExtensionOf: q.type, visibleFrom: scopeOfUse))

    for (concept, ms) in lookup(n.identifier, memberOfTraitVisibleFrom: scopeOfUse) {
      let w = typeOfModel(of: q.type, conformingTo: concept)
      let summonings = summon(w, in: scopeOfUse)

      // TODO: report ambiguous resolution results in the candidate's diagnostics
      assert(summonings.count <= 1)

      for a in summonings {
        for m in ms {
          let w = program.types.reify(
            a.witness, applying: a.substitutions, withVariables: .substitutedByError)
          let u = typeOfImplementation(satisfying: m, in: w)
          candidates.append(.init(reference: .inherited(w, m), type: u))
        }
      }
    }

    return candidates
  }

  /// Returns candidates for resolving `n` as a member declared in the primary declaration of the
  /// type identified by `q`.
  ///
  /// - Requires: `q.type` is not a unification variable.
  private mutating func resolve(
    _ n: Name, nativeMemberOf q: TypedQualification
  ) -> [NameResolutionCandidate] {
    assert(!q.type.isVariable)
    let (receiver, context) = program.types.bodyAndContext(q.type)
    var candidates: [NameResolutionCandidate] = []

    for m in declarations(nativeMembersOf: q.type)[n.identifier] ?? [] {
      var member = declaredType(of: m)
      if let a = program.types[receiver] as? TypeApplication {
        member = program.types.substitute(a.arguments, in: member)
      }
      member = program.types.introduce(context, into: member)
      candidates.append(.init(reference: .member(q.value, m), type: member))
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
          let w = program.types.reify(
            a.witness, applying: a.substitutions, withVariables: .substitutedByError)

          for m in declarations(lexicallyIn: .init(node: e))[n.identifier] ?? [] {
            var member = declaredType(of: m)

            // Strip the context defined by the extension, apply type arguments from the matching
            // witness, and substitute the extendee for the receiver.
            // (member, _) = program.types.bodyAndContext(member)
            if case .typeApplication(_, let arguments) = w.value {
              member = program.types.substitute(arguments, in: member)
            }
            // member = program.types.substitute(s, for: w.type, in: member)
            // member = program.types.introduce(context, into: member)
            result.append(.init(reference: .inherited(w, m), type: member))
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
    switch program.types[program.types.head(t)] {
    case let u as Struct:
      return declarations(lexicallyIn: .init(node: u.declaration))
    case let u as TypeAlias:
      return declarations(nativeMembersOf: u.aliasee)
    case let u as TypeApplication:
      return declarations(nativeMembersOf: u.abstraction)
    default:
      return .init()
    }
  }

  /// Returns the declarations directly contained in `s`.
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

  /// Returns the extensions that are directly contained in `s`.
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
  ///
  /// - Requires: The context clause of `t`, if present, has no usings.
  private mutating func applies(
    _ d: ExtensionDeclaration.ID, to t: AnyTypeIdentity, in s: ScopeIdentity
  ) -> SummonResult? {
    let u = extendeeType(d)
    let w = WitnessExpression(value: .reference(.direct(.init(d))), type: u)

    // Fast path: types are trivially equal.
    if t == u { return .init(witness: w, substitutions: .init()) }

    // Slow path: use the match judgement of implicit resolution to create a witness describing
    // "how" the type matches the extension.
    let (body, context) = program.types.bodyAndContext(t)
    assert(context.usings.isEmpty)
    let thread = ResolutionThread(witness: w, queried: body, environment: .empty, tail: [])
    return takeSummonResults(from: [thread], in: s).uniqueElement
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

  /// Returns the unique identity of a type tree representing the metatype of `t`.
  private mutating func metatype<T: TypeTree>(of t: T) -> Metatype.ID {
    let n = demand(t).erased
    return demand(Metatype(inhabitant: n))
  }

  /// Returns `true` iff the type of `g`'s declaration is being computed.
  private func isOnStack(_ g: Given) -> Bool {
    g.declaration.map(declarationsOnStack.contains(_:)) ?? false
  }

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

  /// Returns the abstraction and argument of `w` if it is a coercion. Otherwise, returns `nil`.
  private func asCoercionApplication(
    _ w: WitnessExpression
  ) -> (coercion: WitnessExpression, argument: WitnessExpression)? {
    if case .termApplication(let a, let b) = w.value, program.types[a.type] is EqualityWitness {
      return (a, b)
    } else {
      return nil
    }
  }

  /// Reports the diagnostic `d`.
  private mutating func report(_ d: Diagnostic) {
    program[module].addDiagnostic(d)
  }

  /// Returns the identity of a fresh type variable.
  private mutating func fresh() -> TypeVariable.ID {
    program.types.fresh()
  }

  /// Returns the unique identity of a tree that is equal to `t`.
  private mutating func demand<T: TypeTree>(_ t: T) -> T.ID {
    program.types.demand(t)
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
