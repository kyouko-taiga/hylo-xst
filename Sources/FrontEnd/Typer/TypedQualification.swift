/// The context in which qualified name resolution takes place.
internal struct TypedQualification {

  /// The expression of the qualification.
  internal let value: DeclarationReference.Qualification

  /// The type of the qualification.
  internal let type: AnyTypeIdentity

}
