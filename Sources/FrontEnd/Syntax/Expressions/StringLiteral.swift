import Archivist

/// The expression of a string literal.
@Archivable
public struct StringLiteral: Expression {

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(site: SourceSpan) {
    self.site = site
  }

  /// The value of the literal.
  public var value: String {
    String(site.text.dropFirst().dropLast())
  }

}

extension StringLiteral: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    String(site.text)
  }

}
