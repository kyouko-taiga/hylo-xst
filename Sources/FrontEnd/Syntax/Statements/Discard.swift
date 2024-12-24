import Archivist

/// The explicit discarding of value.
public struct Discard: Statement {

  /// The value being discarded.
  public let value: ExpressionIdentity

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    "_ = \(program.show(value))"
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
