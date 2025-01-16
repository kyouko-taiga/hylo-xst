/// The declaration of a given.
public enum Given: Hashable {

  /// The built-in given of equality's reflexivity.
  case reflexivity

  /// The built-in given of equality's symmetry.
  case symmetry

  /// The built-in given of equality's transitivity
  case transitivity

  /// A user-defined given.
  case user(DeclarationIdentity)

  /// If declaration of this given if `self` is `.user`. Otherwise, `nil`.
  public var declaration: DeclarationIdentity? {
    if case .user(let d) = self { return d } else { return nil }
  }

}
