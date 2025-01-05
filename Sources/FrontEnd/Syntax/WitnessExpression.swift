/// The expression of a witness produced by implicit resolution.
public struct WitnessExpression: Hashable {

  /// The expression of a witness.
  public indirect enum Value: Hashable {

    case reference(DeclarationReference)

    case application(WitnessExpression, WitnessExpression)

  }

  /// The (synthesized) syntax of the witness.
  public let value: Value

  /// The type of the witness.
  public let type: AnyTypeIdentity

}
