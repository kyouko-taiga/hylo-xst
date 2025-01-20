/// The type of a callable abstraction.
public protocol Callable: TypeTree {

  /// The way in which the abstraction must be applied.
  var style: Call.Style { get }

  /// The input labels and types of the abstraction.
  var inputs: [Parameter] { get }

  /// The the result type of the abstraction, applied mutably iff `isMutating` is `true`.
  func output(calleeIsMutating: Bool) -> AnyTypeIdentity

}

extension Callable {

  /// The labels associated with each input.
  public var labels: some Sequence<String?> {
    inputs.lazy.map(\.label)
  }

}
