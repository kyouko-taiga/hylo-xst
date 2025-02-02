/// The way in which an entity is referred to.
public enum DeclarationReference: Hashable {

  /// A reference to a built-in entity.
  case builtin(BuiltinEntity)

  /// A direct reference.
  case direct(DeclarationIdentity)

  /// A reference to a member declaration.
  case member(DeclarationIdentity)

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
    case .direct(let d), .member(let d), .inherited(_, let d):
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

  /// Returns a copy of `self` in which occurrences of `m` have been substituted for `n`.
  internal func substituting(_ m: ExpressionIdentity, for n: ExpressionIdentity) -> Self {
    if case .inherited(let w, let d) = self {
      return .inherited(w.substituting(m, for: n), d)
    } else {
      return self
    }
  }

}

extension DeclarationReference: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .builtin(let e):
      return "$<builtin \(e)>"
    case .direct(let d), .member(let d), .inherited(_, let d):
      return printer.program.nameOrTag(of: d)
    }
  }

}
