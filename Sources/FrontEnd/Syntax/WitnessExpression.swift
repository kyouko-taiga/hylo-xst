/// The expression of a witness produced by implicit resolution.
public struct WitnessExpression: Hashable {

  /// The expression of a witness.
  public indirect enum Value: Hashable {

    /// An existing term.
    case identity(ExpressionIdentity)

    /// A reference to a term declaration.
    case reference(DeclarationReference)

    /// A context function applied to a term.
    case termApplication(WitnessExpression, WitnessExpression)

    /// A type abstraction applied to type arguments.
    case typeApplication(WitnessExpression, TypeApplication.Arguments)

    /// Returns a copy of `self` in which occurrences of assumed given identified by `i` have been
    /// substituted for `new`.
    public func substituting(assumed i: Int, for new: Value) -> Self {
      switch self {
      case .identity:
        return self

      case .reference(let r):
        return if case .assumed(i, _) = r { new } else { self }

      case .termApplication(let w, let a):
        return .termApplication(
          w.substituting(assumed: i, for: new), a.substituting(assumed: i, for: new))

      case .typeApplication(let w, let ts):
        return .typeApplication(
          w.substituting(assumed: i, for: new), ts)
      }
    }

  }

  /// The (synthesized) syntax of the witness.
  public let value: Value

  /// The type of the witness.
  public let type: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(value: Value, type: AnyTypeIdentity) {
    self.value = value
    self.type = type
  }

  /// Creates a reference to a built-in entity.
  public init(builtin entity: BuiltinEntity, type: AnyTypeIdentity) {
    self.value = .reference(.builtin(entity))
    self.type = type
  }

  /// `true` iff this expression mentions open variable.
  public var hasVariable: Bool {
    if type[.hasVariable] { return true }

    switch value {
    case .identity:
      return false
    case .reference(let r):
      return r.hasVariable
    case .termApplication(let w, let a):
      return w.hasVariable || a.hasVariable
    case .typeApplication(let w, let a):
      return w.hasVariable || a.values.contains(where: { (t) in t[.hasVariable] })
    }
  }

  /// A measure of the size of the deduction tree used to produce the witness.
  public var elaborationCost: Int {
    switch value {
    case .identity, .reference:
      return 0
    case .termApplication(let w, let a):
      return 1 + w.elaborationCost + a.elaborationCost
    case .typeApplication(let w, _):
      return w.elaborationCost
    }
  }

  /// The declaration of the witness evaluated by this expression, if any.
  public var declaration: DeclarationIdentity? {
    switch value {
    case .identity:
      return nil
    case .reference(let r):
      return r.target
    case .termApplication(let w, _), .typeApplication(let w, _):
      return w.declaration
    }
  }

  /// Returns a copy of `self` in which occurrences of assumed given identified by `i` have been
  /// substituted for `new`.
  internal func substituting(assumed i: Int, for new: Value) -> Self {
    .init(value: self.value.substituting(assumed: i, for: new), type: self.type)
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
    case .identity(let e):
      return show(e)
    case .reference(let d):
      return show(d)
    case .termApplication(let w, let a):
      return "\(show(w))(\(show(a)))"
    case .typeApplication(let w, let ts):
      return "\(show(w))<\(format("%T*", [Array(ts.values)]))>"
    }
  }

}
