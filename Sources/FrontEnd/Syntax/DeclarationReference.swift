/// The way in which an entity is referred to.
public indirect enum DeclarationReference: Hashable {

  public enum Qualification: Hashable {

    /// Implicit, as the `.` in `.bar`; the whole name denotes a static member.
    case implicit

    /// Explicit, as `foo.` in `foo.bar` or `.foo.` in `.foo.bar`.
    case explicit(ExpressionIdentity)

  }

  /// A direct reference.
  case direct(DeclarationIdentity)

  /// A reference to a member inherited by conformance.
  case inherited(
    witness: DeclarationReference,
    member: DeclarationIdentity)

}
