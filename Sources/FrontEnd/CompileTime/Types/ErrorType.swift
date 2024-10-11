/// A type denoting a typing error.
public struct ErrorType: TypeTree {

  /// Properties about `self`.
  public var properties: ValueProperties {
    .hasError
  }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    "#?"
  }

}
