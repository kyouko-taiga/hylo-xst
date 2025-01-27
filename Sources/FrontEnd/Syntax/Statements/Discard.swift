import Archivist

/// The explicit discarding of value.
public struct Discard: Statement {

  /// The value being discarded.
  public let value: ExpressionIdentity

  /// The site from which `self` was parsed.
  public let site: SourceSpan

}

extension Discard: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "_ = \(printer.show(value))"
  }

}

extension Discard: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.value = try archive.read(ExpressionIdentity.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(value, in: &context)
    try archive.write(site, in: &context)
  }

}
