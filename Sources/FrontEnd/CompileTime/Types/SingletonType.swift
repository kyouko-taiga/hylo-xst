/// The type of all values equal to a particular expression.
public struct SingletonType: TypeTree {

  /// The expression of the values having the described by `self`.
  public let expression: Denotation

  /// The type of `expression`.
  public let label: AnyTypeIdentity

  /// Properties about `self`.
  public var properties: ValueProperties {
    label.properties
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> SingletonType {
    .init(expression: expression, label: store.map(label, transform))
  }

}

extension SingletonType: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "#exactly(\(printer.show(expression)))"
  }

}
