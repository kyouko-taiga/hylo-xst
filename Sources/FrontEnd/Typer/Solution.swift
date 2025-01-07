import OrderedCollections

/// A table mapping a name component to its declaration.
internal typealias BindingTable = OrderedDictionary<NameExpression.ID, DeclarationReference>

/// The solution of a type constraint system.
internal struct Solution {

  /// The type and term substitutions made by the solver.
  internal private(set) var substitutions: SubstitutionTable

  /// The name binding assumptions made by the solver.
  internal private(set) var bindings: BindingTable

  /// A table from call expression to its arguments after elaboration.
  internal private(set) var elaborations: [(Call.ID, ParameterBindings)] = []

  /// The diagnostics associated with the solution.
  internal let diagnostics: DiagnosticSet

  /// Creates an instance with the given properties.
  internal init(
    substitutions: SubstitutionTable = .init(),
    bindings: BindingTable = .init(),
    elaborations: [(Call.ID, ParameterBindings)] = .init(),
    diagnostics: DiagnosticSet = .init()
  ) {
    self.substitutions = substitutions
    self.bindings = bindings
    self.elaborations = elaborations
    self.diagnostics = diagnostics
  }

}
