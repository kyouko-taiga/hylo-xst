import Archivist

/// A pattern for extracting values with an extractor.
@Archivable
public struct ExtractorPattern: Pattern {

  /// The expression of the extractor's name.
  public let extractor: ExpressionIdentity

  /// The elements of the pattern.
  public let elements: [LabeledPattern]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(extractor: ExpressionIdentity, elements: [LabeledPattern], site: SourceSpan) {
    self.extractor = extractor
    self.elements = elements
    self.site = site
  }

}

extension ExtractorPattern: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "\(printer.show(extractor))(\(printer.show(elements)))"
  }

}
