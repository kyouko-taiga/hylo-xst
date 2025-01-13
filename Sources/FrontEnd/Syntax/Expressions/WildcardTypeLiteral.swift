import Archivist
import Utilities

/// A wildcard literal.
public struct WildcardTypeLiteral: Expression {

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
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
