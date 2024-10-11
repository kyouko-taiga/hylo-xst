import DequeModule
import OrderedCollections
import Utilities

/// The type inference and checking algorithm of Hylo programs.
public struct Typer {

  /// The module being typed.
  public let module: Program.ModuleIdentity

  /// The program containing the module being typed.
  private var program: Program

  /// A cache for various internal operations.
  private var cache: Cache

  /// Creates an instance assigning types to syntax trees in `m`, which is a module in `p`.
  public init(typing m: Program.ModuleIdentity, in p: consuming Program) {
    self.module = m
    self.program = p
    self.cache = .init(typing: module, in: program)
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

    /// The cache of `Typer.lookup(_:lexicallyIn:)`.
    var scopeToIdentifierToDeclarations: [ScopeIdentity: LookupTable]

    /// Creates an instance for typing `m`, which is a module in `p`.
    init(typing m: Program.ModuleIdentity, in p: Program) {
      moduleToIdentifierToDeclaration = .init(repeating: nil, count: p.modules.count)
      sourceToImports = .init(repeating: nil, count: p[m].sources.count)
      scopeToIdentifierToDeclarations = [:]
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

    var inputs: [AnyTypeIdentity] = []
    for p in program[d].parameters {
      inputs.append(declaredType(of: p))
    }

    fatalError()
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

  // MARK: Type inference

  /// Returns the inferred type of `e`, charing `o` with proof obligations and using `hint` to
  /// extract contextual information.
  private mutating func inferredType(
    of e: ExpressionIdentity, charging o: inout Obligations,
    expecting hint: AnyTypeIdentity? = nil
  ) -> AnyTypeIdentity {
    switch program.kind(of: e) {
    case BooleanLiteral.self:
      return inferredType(
        of: program.castUnchecked(e, to: BooleanLiteral.self), charging: &o, expecting: hint)
    case NameExpression.self:
      return inferredType(
        of: program.castUnchecked(e, to: NameExpression.self), charging: &o, expecting: hint)
    case RemoteTypeExpression.self:
      return inferredType(
        of: program.castUnchecked(e, to: RemoteTypeExpression.self), charging: &o, expecting: hint)
    default:
      program.unexpected(e)
    }
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: BooleanLiteral.ID, charging o: inout Obligations,
    expecting hint: AnyTypeIdentity? = nil
  ) -> AnyTypeIdentity {
    fatalError("TODO")
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: NameExpression.ID, charging o: inout Obligations,
    expecting hint: AnyTypeIdentity? = nil
  ) -> AnyTypeIdentity {
    resolve(e, charging: &o)
  }

  /// Returns the inferred type of `e`.
  private mutating func inferredType(
    of e: RemoteTypeExpression.ID, charging o: inout Obligations,
    expecting hint: AnyTypeIdentity? = nil
  ) -> AnyTypeIdentity {
    let t = inferredType(of: program[e].projectee, charging: &o)
    return program.types.demand(RemoteType(projectee: t, access: program[e].access.value))^
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
    var o = Obligations()
    let t = inferredType(of: e, charging: &o)
    let s = discharge(o, relatedTo: e)
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

  /// The result of name resolution for a given expression.
  private enum NameResolutionResult {

    /// Name resolution completed for the longest prefix that can be resolved without involving any
    /// constraint solving.
    ///
    /// - Invariant: `resolved` is not empty.
    case completed(resolved: [ResolvedNameComponent], unresolved: [NameExpression.ID])

    /// Name resolution failed.
    case failed

  }

  /// The result of name resolution for a single name component.
  private struct ResolvedNameComponent {

    /// The resolved component.
    let component: NameExpression.ID

    /// The possible results of name resolution for `component`.
    let candidates: [NameResolutionCandidate]

    /// Creates an instance binding `component` to `candidates`.
    init(binding component: NameExpression.ID, to candidates: [NameResolutionCandidate]) {
      precondition(!candidates.isEmpty)
      self.component = component
      self.candidates = candidates
    }

  }

  private mutating func resolve(
    _ e: NameExpression.ID, charging o: inout Obligations, expecting hint: AnyTypeIdentity? = nil
  ) -> AnyTypeIdentity {
    var (unresolved, prefix) = program.components(of: e)

    var qualification: AnyTypeIdentity?
    switch prefix {
    case .none:
      // All components are nominal.
      qualification = nil

    case .implicit:
      // First component is implicit; use the expected type.
      if let h = hint {
        qualification = h
      } else {
        report(.init(.error, "no context to resolve \(program[e].name)", at: program[e].site))
        return .error
      }

    case .explicit(let q):
      // First component is an arbitrary expression; use inference.
      qualification = inferredType(of: q, charging: &o)
    }

    let scopeOfUse = program.parent(containing: e)!
    while let component = unresolved.popLast() {
      // Gather the declarations to which `c` may refer.
      let candidates: [NameResolutionCandidate]
      if let q = qualification {
        candidates = resolve(program[component].name, memberOf: q)
      } else {
        candidates = resolve(program[component].name, unqualifiedIn: scopeOfUse)
      }

      // Fail if there is no candidate.
      if candidates.isEmpty {
        // TODO: Error reporting?
        return .error
      }

      // TODO: Filter out inaccessible candidates

      qualification = assume(component, isBoundTo: candidates, in: &o)
      if program.types[qualification!].isVariable {
        break
      }
    }

    if unresolved.isEmpty {
      return qualification!
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
    _ n: Parsed<Name>, memberOf qualification: AnyTypeIdentity
  ) -> [NameResolutionCandidate] {
    let ds = lookup(n.value.identifier, memberOf: qualification)
    fatalError()
//    var candidates: [NameResolutionCandidate] = []
//    for d in ds {
//      candidates.append(.init(declaration: d, type: declaredType(of: d)))
//    }

//    return candidates
  }

  private func isAccessible(_ d: DeclarationIdentity, in scopeOfUse: ScopeIdentity) -> Bool {
    // TODO
    true
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
      if append(lookup(identifier, notionallyIn: s)) {
        return result
      }
    }

    // Look for top-level declarations in the current scope.
    result.append(contentsOf: lookup(identifier, atTopLevelOf: scopeOfUse.module))
    if !result.isEmpty {
      return result
    }

    // Look for declarations in imports.
    for n in imports(of: scopeOfUse.file) where n != scopeOfUse.module {
      result.append(contentsOf: lookup(identifier, atTopLevelOf: scopeOfUse.module))
    }
    if !result.isEmpty {
      return result
    }

    // TODO: Built-ins

    return result
  }

  /// Returns the declarations introducing `identifier` in the notional scope to which `s` belongs.
  private mutating func lookup(
    _ identifier: String, notionallyIn s: ScopeIdentity
  ) -> [DeclarationIdentity] {
    if let t = nominalScope(including: s) {
      return lookup(identifier, memberOf: t)
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
      let table = lookupTable(declarations: program[m].topLevelDeclarations)
      cache.moduleToIdentifierToDeclaration[m] = table
      return table[identifier] ?? []
    }
  }

  /// Returns the declarations introducing `identifier` in `s`.
  ///
  /// This method only returns declarations that are lexically contained in `s`, which is unlike
  /// `lookup(_:notionallyIn:)` which also returns members declared in extensions.
  private mutating func lookup(
    _ identifier: String, lexicallyIn lexicalScope: ScopeIdentity
  ) -> [DeclarationIdentity] {
    if let table = cache.scopeToIdentifierToDeclarations[lexicalScope] {
      return table[identifier] ?? []
    } else {
      let table = lookupTable(declarations: program.declarations(in: lexicalScope))
      cache.scopeToIdentifierToDeclarations[lexicalScope] = table
      return table[identifier] ?? []
    }
  }

  /// Returns the declarations introducing `identifier` as a member of `qualification`.
  private mutating func lookup(
    _ identifier: String, memberOf qualification: AnyTypeIdentity
  ) -> [DeclarationIdentity] {
    fatalError()
  }

  /// Returns the type defining the nominal scope that includes `s`, if any.
  private mutating func nominalScope(including s: ScopeIdentity) -> AnyTypeIdentity? {
    switch program.kind(of: s) {
    case ClassDeclaration.self:
      return program.types.demand(Class(declaration: program.castUnchecked(s)))^
    case TraitDeclaration.self:
      return program.types.demand(Trait(declaration: program.castUnchecked(s)))^
    default:
      return nil
    }
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

  /// Returns a table mapping the identifiers of the names declared in `ds` to their declarations.
  private func lookupTable<T: Sequence<DeclarationIdentity>>(
    declarations ds: T
  ) -> Cache.LookupTable {
    var m = Cache.LookupTable()
    for d in ds {
      if let n = program[d] as? any TypeDeclaration {
        m[n.identifier.value, default: []].append(d)
      } else if let n = program.cast(d, to: FunctionDeclaration.self) {
        m[program.name(of: n).identifier, default: []].append(d)
      }
    }
    return m
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

}
