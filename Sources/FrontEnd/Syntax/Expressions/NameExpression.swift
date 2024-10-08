import Archivist

/// A reference to an entity.
public struct NameExpression: Expression {

  /// The name of the referred entity.
  public let name: Parsed<Name>

  /// The site from which `self` was parsed.
  public var site: SourceSpan

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String { name.description }

}

extension NameExpression: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.name = try archive.read(Parsed<Name>.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(name, in: &context)
    try archive.write(site, in: &context)
  }

}
