/// The declaration of a given.
public enum Given: Hashable {

  /// The built-in given of a coercion.
  case coercion(EqualityProperty)

  /// A given implied by a constraint defined in a trait.
  case abstract(AnyTypeIdentity)

  /// A given that is assumed during implicit resolution.
  case assumed(Int, AnyTypeIdentity)

  /// A user-defined given.
  case user(DeclarationIdentity)

  /// A given nested in a trait.
  indirect case nested(TraitDeclaration.ID, Given)

  /// Returns `true` iff `self` is `.abstract`.
  public var isAbstract: Bool {
    if case .abstract = self { true } else { false }
  }

  /// If declaration of this given if `self` is `.user`. Otherwise, `nil`.
  public var declaration: DeclarationIdentity? {
    if case .user(let d) = self { d } else { nil }
  }

}
