/// The expression of a witness produced by implicit resolution.
public struct WitnessExpression: Hashable {

  /// The expression of a witness.
  public indirect enum Value: Hashable {

    /// A reference to a term declaration.
    case reference(DeclarationReference)

    /// A context function applied to a term.
    case termApplication(WitnessExpression, WitnessExpression)

    /// A type abstraction applied to type arguments.
    case typeApplication(WitnessExpression, [AnyTypeIdentity])

    public func substituting(_ old: Value, for new: Value) -> Self {
      switch self {
      case old:
        return new
      case .reference:
        return self
      case .termApplication(let w, let a):
        return .termApplication(w.substituting(old, for: new), a.substituting(old, for: new))
      case .typeApplication(let w, let ts):
        return .typeApplication(w.substituting(old, for: new), ts)
      }
    }

  }

  /// The (synthesized) syntax of the witness.
  public let value: Value

  /// The type of the witness.
  public let type: AnyTypeIdentity

  /// `true` iff this expression mentions open variable.
  public var hasVariable: Bool {
    if type[.hasVariable] { return true }

    switch value {
    case .reference(let r):
      return r.hasVariable
    case .termApplication(let w, let a):
      return w.hasVariable || a.hasVariable
    case .typeApplication(let w, let a):
      return w.hasVariable || a.contains(where: { (t) in t[.hasVariable] })
    }
  }

  /// A measure of the size of the deduction tree used to produce the witness.
  public var elaborationCost: Int {
    switch value {
    case .reference:
      return 0
    case .termApplication(let w, let a):
      return 1 + w.elaborationCost + a.elaborationCost
    case .typeApplication(let w, _):
      return w.elaborationCost
    }
  }

  /// The reference to the declaration of the witness evaluated by this expression.
  public var declaration: DeclarationReference {
    switch value {
    case .reference(let d):
      return d
    case .termApplication(let w, _), .typeApplication(let w, _):
      return w.declaration
    }
  }

  public func substituting(_ old: Value, for new: Value) -> Self {
    .init(value: self.value.substituting(old, for: new), type: self.type)
  }

}

extension Program {

  /// Returns a debug representation of `w`.
  public func show(_ w: WitnessExpression) -> String {
    show(w.value)
  }

  /// Returns a debug representation of `v`.
  public func show(_ v: WitnessExpression.Value) -> String {
    switch v {
    case .reference(let d):
      return show(d)
    case .termApplication(let w, let a):
      return "\(show(w))(\(show(a)))"
    case .typeApplication(let w, let ts):
      return "\(show(w))<\(format("%T*", [ts]))>"
    }
  }

}
