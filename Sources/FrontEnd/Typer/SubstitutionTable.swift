/// A substitution table mapping type and term variables to their values.
internal struct SubstitutionTable {

  /// A policy for substituting variables during reification.
  internal enum SubstitutionPolicy {

    /// Free variables are substituted by errors.
    case substitutedByError

    /// Free variables are kept.
    case kept

  }

  /// Returns a copy of `t`, which is defined in `p`, where each variable is substituted by either
  /// its corresponding value in `self` or the application of `substitutionPolicy` is no such
  /// substitution exists.
  ///
  /// The default substitution policy is `substituteByError` because we typically use `reify` on
  /// fully formed solutions, thus not expecting any open variables.
  internal func reify(
    _ t: AnyTypeIdentity, definedIn p: inout Program,
    withVariables substitutionPolicy: SubstitutionPolicy = .substitutedByError
  ) -> AnyTypeIdentity {
    t
  }

}
