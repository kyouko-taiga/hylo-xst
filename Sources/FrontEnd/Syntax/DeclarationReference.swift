/// The way in which an entity is referred to.
public indirect enum DeclarationReference: Hashable {

  public enum Qualification: Hashable {

    /// Implicit, as the `.` in `.bar`; the whole name denotes a static member.
    case implicit

    /// Explicit, as `foo.` in `foo.bar` or `.foo.` in `.foo.bar`.
    case explicit(ExpressionIdentity)

  }

  /// A reference to a predefined entity.
  case predefined

  /// A direct reference.
  case direct(DeclarationIdentity)

  /// A reference to a member inherited by conformance.
  case inherited(
    witness: WitnessExpression,
    member: DeclarationIdentity)

}

extension Program {

  /// Returns a source-like representation of `r`.
  public func show(_ r: DeclarationReference) -> String {
    switch r {
    case .predefined:
      return "predefined"
    case .direct(let d):
      return name(of: d)?.description ?? "$<\(kind(of: d))>"
    case .inherited(_, let m):
      return name(of: m)?.description ?? "$<\(kind(of: m))>"
    }
  }

}
