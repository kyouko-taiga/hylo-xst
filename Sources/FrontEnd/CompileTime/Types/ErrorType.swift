/// A type denoting a typing error.
public struct ErrorType: TypeTree {

  /// Properties about `self`.
  public var properties: ValueProperties {
    .hasError
  }

}

extension ErrorType: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "#!"
  }

}
