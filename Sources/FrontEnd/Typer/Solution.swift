/// The solution of a type constraint system.
internal struct Solution {

  /// The type and term substitutions made by the solver.
  internal private(set) var substitutions: SubstitutionTable

  /// Creates an empty solution.
  internal init() {
    self.substitutions = .init()
  }

}
