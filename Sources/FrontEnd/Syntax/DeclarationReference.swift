/// The way in which an entity is referred to.
public indirect enum DeclarationReference: Hashable {

  /// The qualification of a reference to a member declaration.
  public enum Qualification: Hashable {

    /// Virtual, for the purpose of applying name resolution.
    case virtual

    /// Explicit, as `foo.` in `foo.bar` or `.foo.` in `.foo.bar`.
    case explicit(ExpressionIdentity)

  }

  /// A reference to a built-in entity.
  case builtin(BuiltinEntity)

  /// A direct reference.
  case direct(DeclarationIdentity)

  /// A reference to a member declaration.
  case member(Qualification, DeclarationIdentity)

  /// A reference to a member inherited by conformance or extension.
  case inherited(WitnessExpression, DeclarationIdentity)

  /// `true` iff this referennce mentions open variable.
  public var hasVariable: Bool {
    switch self {
    case .builtin, .direct, .member:
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
    case .builtin, .direct, .member:
      return 0
    case .inherited(let w, _):
      return 1 + w.elaborationCost
    }
  }

}

extension DeclarationReference: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .builtin(let e):
      return "$<builtin \(e)>"
    case .direct(let d):
      return printer.program.nameOrTag(of: d)
    case .member(let q, let d):
      return printer.show(q) + "." + printer.program.nameOrTag(of: d)
    case .inherited(_, let d):
      return printer.program.nameOrTag(of: d)
    }
  }

}

extension DeclarationReference.Qualification: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .virtual:
      return "$virtual"
    case .explicit(let e):
      return printer.show(e)
    }
  }

}
