import OrderedCollections

/// A set of formulae to be proven for checking the type of a syntax tree.
internal struct Obligations {

  /// A set of constraints to solve.
  internal private(set) var constraints: [any Constraint]

  /// A table from syntax tree to its type.
  internal private(set) var syntaxToType: OrderedDictionary<AnySyntaxIdentity, AnyTypeIdentity>

  /// A table from name component to its declaration.
  internal private(set) var bindings: BindingTable

  /// `true` iff a this set cannot be discharged because.
  internal private(set) var isUnsatisfiable: Bool

  /// Creates an empty set.
  internal init() {
    self.constraints = []
    self.syntaxToType = [:]
    self.bindings = [:]
    self.isUnsatisfiable = false
  }

  /// Marks `self` to be unsatisfiable.
  internal mutating func setUnsatisfiable() {
    isUnsatisfiable = true
  }

  /// Assumes that `k` holds.
  internal mutating func assume(_ k: any Constraint) {
    if !k.isTrivial { constraints.append(k) }
  }

  /// Assumes that `n` refers to `r`.
  internal mutating func assume(_ n: NameExpression.ID, boundTo r: DeclarationReference) {
    bindings[n] = r
  }

  /// Assumes that `n` `n` has type `t` and returns `t`.
  @discardableResult
  internal mutating func assume<T: SyntaxIdentity>(
    _ n: T, hasType t: AnyTypeIdentity, at site: SourceSpan
  ) -> AnyTypeIdentity {
    if let u = syntaxToType[n.erased] {
      assume(TypeEquality(lhs: t, rhs: u, site: site))
    } else {
      syntaxToType[.init(n)] = t
    }

    if t[.hasError] { setUnsatisfiable() }
    return t
  }

  internal typealias PostCheck = (
    _ s: Solution,
    _ p: inout Program,
    _ d: inout DiagnosticSet
  ) -> Void

  internal mutating func finally(_ callback: @escaping PostCheck) {

  }

}
