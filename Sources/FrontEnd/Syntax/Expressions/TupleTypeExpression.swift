import Archivist

/// The expression of a tuple type.
@Archivable
public struct TupleTypeExpression: Expression {

  /// The elements of the tuple.
  public let elements: [LabeledExpression]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(elements: [LabeledExpression], site: SourceSpan) {
    self.elements = elements
    self.site = site
  }

}

extension TupleTypeExpression: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "{\(printer.show(elements))}"
  }

}
