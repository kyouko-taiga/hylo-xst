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

  }

  /// The (synthesized) syntax of the witness.
  public let value: Value

  /// The type of the witness.
  public let type: AnyTypeIdentity

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

}
