import DequeModule
import OrderedCollections
import MoreCollections
import Utilities

/// The type inference and checking algorithm of Hylo programs.
public struct Typer {

  /// The module being typed.
  public let module: Program.ModuleIdentity

  /// The program containing the module being typed.
  private var program: Program

  /// A cache for various internal operations.
  private var cache: Cache

  /// The set of extensions to ignore during name resolution.
  private var extensionsToIgnore: SortedSet<ExtensionDeclaration.ID>

  /// Creates an instance assigning types to syntax trees in `m`, which is a module in `p`.
  public init(typing m: Program.ModuleIdentity, in p: consuming Program) {
    self.module = m
    self.program = p
    self.cache = .init(typing: module, in: program)
    self.extensionsToIgnore = []
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
  private struct Cache {

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

    /// Creates an instance for typing `m`, which is a module in `p`.
    init(typing m: Program.ModuleIdentity, in p: Program) {
      self.moduleToIdentifierToDeclaration = .init(repeating: nil, count: p.modules.count)
      self.sourceToImports = .init(repeating: nil, count: p[m].sources.count)
      self.scopeToExtensions = [:]
      self.scopeToLookupTable = [:]
      self.scopeToTypeToLookupTable = [:]
    }

  }

  // MARK: Type checking

  /// Type checks `d`.
  private mutating func check(_ d: DeclarationIdentity) {
    switch program.kind(of: d) {
    case AssociatedTypeDeclaration.self:
      check(program.castUnchecked(d, to: AssociatedTypeDeclaration.self))
    case ClassDeclaration.self:
      check(program.castUnchecked(d, to: ClassDeclaration.self))
    case ExtensionDeclaration.self:
      check(program.castUnchecked(d, to: ExtensionDeclaration.self))
    case FunctionDeclaration.self:
      check(program.castUnchecked(d, to: FunctionDeclaration.self))
    case TraitDeclaration.self:
      check(program.castUnchecked(d, to: TraitDeclaration.self))
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
  private mutating func check(_ d: ClassDeclaration.ID) {
    _ = declaredType(of: d)
    // TODO
  }

  /// Type checks `d`.
  private mutating func check(_ d: ExtensionDeclaration.ID) {
    // TODO
  }

  /// Type checks `d`.
  private mutating func check(_ d: FunctionDeclaration.ID) {
    _ = declaredType(of: d)
    // TODO
  }

  /// Type checks `d`.
  private mutating func check(_ d: TraitDeclaration.ID) {
    _ = declaredType(of: d)
    // TODO
  }

  /// Returns the declared type of `d` without type checking its contents.
  private mutating func declaredType(of d: DeclarationIdentity) -> AnyTypeIdentity {
    switch program.kind(of: d) {
    case AssociatedTypeDeclaration.self:
      return declaredType(of: program.castUnchecked(d, to: AssociatedTypeDeclaration.self))
    case ClassDeclaration.self:
      return declaredType(of: program.castUnchecked(d, to: ClassDeclaration.self))
    case FunctionDeclaration.self:
      return declaredType(of: program.castUnchecked(d, to: FunctionDeclaration.self))
    case TraitDeclaration.self:
      return declaredType(of: program.castUnchecked(d, to: AssociatedTypeDeclaration.self))
    default:
      program.unexpected(d)
    }
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: AssociatedTypeDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[module].type(assignedTo: d) { return memoized }

    let p = program.parent(containing: d, as: TraitDeclaration.self)!
    let q = demand(Trait(declaration: p))^
    let t = demand(AssociatedType(declaration: d, qualification: q))^
    let u = demand(Metatype(inhabitant: t))^
    program[module].setType(u, for: d)
    return u
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: ClassDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[module].type(assignedTo: d) { return memoized }

    let t = demand(Class(declaration: d))^
    let u = demand(Metatype(inhabitant: t))^
    program[module].setType(u, for: d)
    return u
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: FunctionDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[module].type(assignedTo: d) { return memoized }

    var inputs: [Parameter] = []
    for p in program[d].parameters {
      inputs.append(
        Parameter(
          label: program[p].label?.value,
          type: declaredType(of: p),
          hasDefault: false,
          isImplicit: false))
    }

    let output = program[d].output.map { (a) in
      evaluateTypeAscription(a)
    }

    let t = demand(Arrow(inputs: inputs, output: output ?? .void))^
    program[module].setType(t, for: d)
    return t
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
  private mutating func declaredType(of d: TraitDeclaration.ID) -> AnyTypeIdentity {
    if let memoized = program[module].type(assignedTo: d) { return memoized }

    let t = demand(Trait(declaration: d))^
    let u = demand(Metatype(inhabitant: t))^
    program[module].setType(u, for: d)
    return u
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

  // MARK: Type inference

  /// The context in which the type of a syntax tree is being inferred.
  private struct InferenceContext {

    /// The type expected to be inferred given the context.
    let expectedType: AnyTypeIdentity?

    /// A set of formulae about the type being inferred.
    var obligations: Obligations

    /// Creates a context with the given properties.
    init(expectedType: AnyTypeIdentity? = nil) {
      self.expectedType = expectedType
      self.obligations = .init()
    }

  }

  /// Returns the inferred type of `e`, which occurs in `context`.
  private mutating func inferredType(
    of e: ExpressionIdentity, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    switch program.kind(of: e) {
    case BooleanLiteral.self:
      return inferredType(
        of: program.castUnchecked(e, to: BooleanLiteral.self), in: &context)
    case NameExpression.self:
      return inferredType(
        of: program.castUnchecked(e, to: NameExpression.self), in: &context)
    case RemoteTypeExpression.self:
      return inferredType(
        of: program.castUnchecked(e, to: RemoteTypeExpression.self), in: &context)
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
    of e: NameExpression.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    resolve(e, in: &context)
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: RemoteTypeExpression.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    let t = evaluateTypeAscription(program[e].projectee)
    let u = demand(RemoteType(projectee: t, access: program[e].access.value))^
    let v = demand(Metatype(inhabitant: u))^
    return assume(e, hasType: v, in: &context.obligations)
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
      return assume(n, hasType: pick.type, in: &o)
    }

    fatalError("TODO")
  }

  /// Constrains `n` to have type `t` in `o` and returns `t`.
  @discardableResult
  private mutating func assume<T: SyntaxIdentity>(
    _ n: T, hasType t: AnyTypeIdentity, in o: inout Obligations
  ) -> AnyTypeIdentity {
    if t[.hasError] { o.setUnsatisfiable() }

//    // Accumulate constraints on previous choices.
//    if let u = o.syntaxToType[e] {
//      if areEquivalent(t, u, in: program[e].scope) { return u }
//      obligations.insert(EqualityConstraint(t, u, origin: .init(.structural, at: program[e].site)))
//      return u
//    }

    o.assume(.init(n), instanceOf: t)
    return t
  }

  /// Proves the obligations `o`, which relate to the well-typedness of `n`, returning the best
  /// assignment of universally quantified variables.
  @discardableResult
  private mutating func discharge<T: SyntaxIdentity>(
    _ o: Obligations, relatedTo n: T
  ) -> Solution {
    // TODO
    Solution()
  }


  // MARK: Compile-time evaluation

  /// Evaluates `e` as a type ascription.
  private mutating func evaluateTypeAscription(_ e: ExpressionIdentity) -> AnyTypeIdentity {
    var c = InferenceContext()
    let t = inferredType(of: e, in: &c)
    let s = discharge(c.obligations, relatedTo: e)
    let u = s.substitutions.reify(t, definedIn: &program)

    if let m = program.types[u] as? Metatype {
      return m.inhabitant
    } else {
      report(.init(.error, "expression does not denote a type", at: program[e].site))
      return .error
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

  private struct NameResolutionContexxt {

    let qualification: DeclarationReference.Qualification

    let type: AnyTypeIdentity

  }

  private mutating func resolve(
    _ e: NameExpression.ID, in context: inout InferenceContext
  ) -> AnyTypeIdentity {
    var (unresolved, prefix) = program.components(of: e)

    var qualification: NameResolutionContexxt?
    switch prefix {
    case .none:
      // All components are nominal.
      qualification = nil

    case .implicit:
      // First component is implicit; use the expected type.
      if let h = context.expectedType {
        qualification = .init(qualification: .implicit, type: h)
      } else {
        report(.init(.error, "no context to resolve \(program[e].name)", at: program[e].site))
        return .error
      }

    case .explicit(let e):
      // First component is an arbitrary expression; use inference.
      let t = inferredType(of: e, in: &context)
      qualification = .init(qualification: .explicit(e), type: t)
    }

    let scopeOfUse = program.parent(containing: e)
    while let component = unresolved.popLast() {
      // Gather the declarations to which `c` may refer.
      let candidates: [NameResolutionCandidate]
      if let q = qualification {
        candidates = resolve(program[component].name, memberOf: q, visibleFrom: scopeOfUse)
      } else {
        candidates = resolve(program[component].name, unqualifiedIn: scopeOfUse)
      }

      // Fail if there is no candidate.
      if candidates.isEmpty {
        // TODO: Error reporting?
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
    _ n: Parsed<Name>, unqualifiedIn scopeOfUse: ScopeIdentity
  ) -> [NameResolutionCandidate] {
    let ds = lookup(n.value.identifier, unqualifiedIn: scopeOfUse)

    var candidates: [NameResolutionCandidate] = []
    for d in ds {
      candidates.append(.init(reference: .direct(d), type: declaredType(of: d)))
    }

    return candidates
  }

  private mutating func resolve(
    _ n: Parsed<Name>, memberOf qualification: NameResolutionContexxt,
    visibleFrom scopeOfUse: ScopeIdentity
  ) -> [NameResolutionCandidate] {
    let ds = lookup(n.value.identifier, memberOf: qualification.type, visibleFrom: scopeOfUse)

    var candidates: [NameResolutionCandidate] = []
    for d in ds {
      candidates.append(.init(reference: .direct(d), type: declaredType(of: d)))
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
      if append(lookup(identifier, logicallyIn: s, visibleFrom: scopeOfUse)) {
        return result
      }
    }

    // Look for top-level declarations in other source files.
    let f = scopeOfUse.file
    for s in program[f.module].sourceFileIdentities where s != f {
      if append(lookup(identifier, logicallyIn: .init(file: s), visibleFrom: scopeOfUse)) {
        return result
      }
    }

    // Look for imports.
    for n in imports(of: f) {
      result.append(contentsOf: lookup(identifier, atTopLevelOf: n))
    }
    if !result.isEmpty { return result }

    // TODO: Built-ins

    return result
  }

  /// Returns the declarations that introduce `identifier` in the logical scope of `s` and that are
  /// visible from `scopeOfUse`.
  private mutating func lookup(
    _ identifier: String, logicallyIn s: ScopeIdentity,
    visibleFrom scopeOfUse: ScopeIdentity
  ) -> [DeclarationIdentity] {
    if let t = nominalScope(including: s) {
      return lookup(identifier, memberOf: t, visibleFrom: scopeOfUse)
    } else {
      return lookup(identifier, lexicallyIn: s)
    }
  }

  /// Returns the top-level declarations of `m` introducing `identifier`.
  private mutating func lookup(
    _ identifier: String, atTopLevelOf m: Program.ModuleIdentity
  ) -> [DeclarationIdentity] {
    if let table = cache.moduleToIdentifierToDeclaration[m] {
      return table[identifier] ?? []
    } else {
      var table = Cache.LookupTable()
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

  /// Returns the declarations that introduce a member of `t` and are visible from `s`.
  private mutating func declarations(
    memberOf t: AnyTypeIdentity, visibleFrom s: ScopeIdentity
  ) -> Cache.LookupTable {
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
      where !extensionsToIgnore.contains(d) && applies(d, to: t) {
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
        where !extensionsToIgnore.contains(d) && applies(d, to: t) {
          extendLookupTable(&table, with: program[d].members)
        }
      }
      cache.scopeToTypeToLookupTable[Scoped(t, in: s)] = table
      return table
    }
  }

  /// Returns the declarations lexically contained in the declaration of `t`.
  private mutating func declarations(nativeMembersOf t: AnyTypeIdentity) -> Cache.LookupTable {
    switch program.types[t] {
    case let u as Class:
      return declarations(lexicallyIn: .init(node: u.declaration))
    default:
      return .init()
    }
  }

  /// Returns the declarations lexically contained in `s`.
  private mutating func declarations(lexicallyIn s: ScopeIdentity) -> Cache.LookupTable {
    if let table = cache.scopeToLookupTable[s] {
      return table
    } else {
      var table = Cache.LookupTable()
      extendLookupTable(&table, with: program.declarations(in: s))
      cache.scopeToLookupTable[s] = table
      return table
    }
  }

  /// Returns the extensions that are lexically contained in `s`.
  private mutating func extensions(lexicallyIn s: ScopeIdentity) -> [ExtensionDeclaration.ID] {
    if let ds = cache.scopeToExtensions[s] {
      return ds
    } else {
      let ds = program.collect(ExtensionDeclaration.self, in: program.declarations(in: s))
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
        if let m = program.identity(module: program[i].name.value) { table.append(m) }
      }
      cache.sourceToImports[f.offset] = table
      return table
    }
  }

  /// Extends `m` so that it maps identifiers declared in `ds` to their declarations.
  private func extendLookupTable<T: Sequence<DeclarationIdentity>>(
    _ m: inout Cache.LookupTable, with ds: T
  ) {
    for d in ds {
      if let n = program[d] as? any TypeDeclaration {
        m[n.identifier.value, default: []].append(d)
      } else if let n = program.cast(d, to: FunctionDeclaration.self) {
        m[program.name(of: n).identifier, default: []].append(d)
      }
    }
  }

  /// Returns the type defining the nominal scope that includes `s`, if any.
  private mutating func nominalScope(including s: ScopeIdentity) -> AnyTypeIdentity? {
    // Exit early if `s` is a file.
    guard let n = s.node else { return nil }

    // Only types have nominal scopes.
    switch program.kind(of: n) {
    case ClassDeclaration.self:
      return program.types.demand(Class(declaration: program.castUnchecked(n)))^
    case TraitDeclaration.self:
      return program.types.demand(Trait(declaration: program.castUnchecked(n)))^
    default:
      return nil
    }
  }

  // MARK: Helpers

  /// Reports the diagnostic `d`.
  private mutating func report(_ d: Diagnostic) {
    program[module].addDiagnostic(d)
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
    extensionsToIgnore.insert(d)
    defer { extensionsToIgnore.remove(d) }
    return action(&self)
  }

}
