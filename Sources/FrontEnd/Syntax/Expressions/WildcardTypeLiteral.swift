import Archivist

/// A wildcard literal.
public struct WildcardTypeLiteral: Expression {

  /// The site from which `self` was parsed.
  public let site: SourceSpan

}

extension WildcardTypeLiteral: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "_"
  }

}

extension WildcardTypeLiteral: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(site, in: &context)
  }

}
