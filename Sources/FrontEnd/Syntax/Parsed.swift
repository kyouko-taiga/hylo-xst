import Archivist

/// A construct whose representation was parsed from a source files.
public struct Parsed<T> {

  /// The parsed construct.
  public let value: T

  /// The site from which `self` was extracted.
  public let site: SourceSpan

  /// Creates an instance annotating its value with the site from which it was extracted.
  public init(_ value: T, at site: SourceSpan) {
    self.value = value
    self.site = site
  }

}

extension Parsed: Equatable where T: Equatable {}

extension Parsed: Hashable where T: Hashable {}

extension Parsed: CustomStringConvertible {

  public var description: String {
    String(describing: value)
  }

}

extension Parsed: Archivable where T: Archivable {

  public init<U>(from archive: inout ReadableArchive<U>, in context: inout Any) throws {
    self.value = try archive.read(T.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<U>(to archive: inout WriteableArchive<U>, in context: inout Any) throws {
    try archive.write(value, in: &context)
    try archive.write(site, in: &context)
  }

}
