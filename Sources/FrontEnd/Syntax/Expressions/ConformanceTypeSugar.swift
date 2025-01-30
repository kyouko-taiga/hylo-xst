/// The sugared expression of the type of a conformance witness.
public struct ConformanceTypeSugar {

  /// The desugared representation of `self`.
  public let desugared: StaticCall

  /// Creates an instance presenting the given desugared representation.
  ///
  /// - Requires: `desugared` as at least one argument.
  public init(_ desugared: StaticCall) {
    assert(!desugared.arguments.isEmpty)
    self.desugared = desugared
  }

  /// The expression of the conforming type.
  public var conformer: ExpressionIdentity {
    desugared.arguments[0]
  }

  /// The expression of the trait to which the type conforms.
  public var concept: ExpressionIdentity {
    desugared.callee
  }

  /// The additional arguments of the trait.
  public var arguments: ArraySlice<ExpressionIdentity> {
    desugared.arguments.dropFirst()
  }

}
