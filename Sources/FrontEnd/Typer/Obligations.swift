import OrderedCollections

/// A set of formulae to be proven for checking the type of a syntax tree.
internal struct Obligations {

  /// A set of constraints to solve.
  internal private(set) var constraints: [any Constraint]

  /// A table from syntax tree to its type.
  internal private(set) var syntaxToType: [AnySyntaxIdentity: AnyTypeIdentity]

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
    constraints.append(k)
  }

  /// Assumes that `n` has type `t`.
  internal mutating func assume(_ n: AnySyntaxIdentity, instanceOf t: AnyTypeIdentity) {
    syntaxToType[n] = t
  }

  /// Assumes that `n` refers to `r`.
  internal mutating func assume(_ n: NameExpression.ID, isBoundTo r: DeclarationReference) {
    bindings[n] = r
  }

}
