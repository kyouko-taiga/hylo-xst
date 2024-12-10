import OrderedCollections

/// A table mapping a name component to its declaration.
internal typealias BindingTable = OrderedDictionary<NameExpression.ID, DeclarationReference>

/// The solution of a type constraint system.
internal struct Solution {

  /// The type and term substitutions made by the solver.
  internal private(set) var substitutions: SubstitutionTable

  /// The name binding assumptions made by the solver.
  internal private(set) var bindings: BindingTable

  /// Creates an empty solution.
  internal init() {
    self.substitutions = .init()
    self.bindings = .init()
  }

  /// Creates an instance with the given properties.
  internal init(
    substitutions: SubstitutionTable,
    bindings: BindingTable
  ) {
    self.substitutions = substitutions
    self.bindings = bindings
  }

}
