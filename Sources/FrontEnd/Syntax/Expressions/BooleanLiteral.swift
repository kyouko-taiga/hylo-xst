import Archivist
import Utilities

/// The expression of a Boolean literal.
public struct BooleanLiteral: Expression {

  /// The site from which `self` was parsed.
  public var site: SourceSpan

  /// The value of the literal.
  public var value: Bool { site.text == "true" }

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String { value.description }

}

extension BooleanLiteral: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(site, in: &context)
  }

}
