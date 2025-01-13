/// The way in which an entity is referred to.
public indirect enum DeclarationReference: Hashable {

  /// The qualification of a reference to a member declaration.
  public enum Qualification: Hashable {

    /// Virtual, for the purpose of applying name resolution.
    case virtual

    /// Implicit, as the `.` in `.bar`; the whole name denotes a static member.
    case implicit

    /// Explicit, as `foo.` in `foo.bar` or `.foo.` in `.foo.bar`.
    case explicit(ExpressionIdentity)

  }

  /// A reference to a predefined entity.
  case predefined

  /// A direct reference.
  case direct(DeclarationIdentity)

  /// A reference to a member declaration.
  case member(Qualification, DeclarationIdentity)

  /// A reference to a member inherited by conformance or extension.
  case inherited(WitnessExpression, DeclarationIdentity)

  /// `true` iff this referennce mentions open variable.
  public var hasVariable: Bool {
    switch self {
    case .predefined, .direct, .member:
      return false
    case .inherited(let w, _):
      return w.hasVariable
    }
  }

  /// The referred declaration, unless it is predefined.
  public var target: DeclarationIdentity? {
    switch self {
    case .direct(let d), .member(_, let d), .inherited(_, let d):
      return d
    default:
      return nil
    }
  }

  /// A measure of the complexity of reference's elaborated expression.
  public var elaborationCost: Int {
    switch self {
    case .predefined, .direct, .member:
      return 0
    case .inherited(let w, _):
      return 1 + w.elaborationCost
    }
  }

}

extension Program {

  /// Returns a source-like representation of `r`.
  public func show(_ r: DeclarationReference) -> String {
    switch r {
    case .predefined:
      return "$predefined"
    case .direct(let d):
      return nameOrTag(of: d)
    case .member(let q, let d):
      return show(q) + "." + nameOrTag(of: d)
    case .inherited(_, let d):
      return nameOrTag(of: d)
    }

    func nameOrTag(of d: DeclarationIdentity) -> String {
      name(of: d)?.description ?? "$<\(tag(of: d))>"
    }
  }

  /// Returns a source-like representation of `q`.
  public func show(_ q: DeclarationReference.Qualification) -> String {
    switch q {
    case .virtual:
      return "$virtual"
    case .implicit:
      return ""
    case .explicit(let e):
      return show(e)
    }
  }

}
