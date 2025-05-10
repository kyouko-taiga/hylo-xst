import Archivist

/// The explicit discarding of value.
@Archivable
public struct Discard: Statement {

  /// The value being discarded.
  public let value: ExpressionIdentity

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(value: ExpressionIdentity, site: SourceSpan) {
    self.value = value
    self.site = site
  }

}

extension Discard: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "_ = \(printer.show(value))"
  }

}
