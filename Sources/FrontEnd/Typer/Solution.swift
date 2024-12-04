import OrderedCollections

/// The solution of a type constraint system.
internal struct Solution {

  /// The type and term substitutions made by the solver.
  internal private(set) var substitutions: SubstitutionTable

  /// The name binding assumptions made by the solver.
  internal private(set) var bindings:
    OrderedDictionary<NameExpression.ID, DeclarationReference>

  /// Creates an empty solution.
  internal init() {
    self.substitutions = .init()
    self.bindings = .init()
  }

  /// Creates an instance with the given properties.
  internal init(
    substitutions: SubstitutionTable,
    bindings: OrderedDictionary<NameExpression.ID, DeclarationReference>
  ) {
    self.substitutions = substitutions
    self.bindings = bindings
  }

}
