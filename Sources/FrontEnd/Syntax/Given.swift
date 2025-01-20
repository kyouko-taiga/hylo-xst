/// The declaration of a given.
public enum Given: Hashable {

  /// The built-in given of a coercion.
  case coercion(EqualityProperty)

  /// A given that is assumed during implicit resolution.
  case assumed(AnyTypeIdentity)

  /// A user-defined given.
  case user(DeclarationIdentity)

  /// If declaration of this given if `self` is `.user`. Otherwise, `nil`.
  public var declaration: DeclarationIdentity? {
    if case .user(let d) = self { return d } else { return nil }
  }

}
