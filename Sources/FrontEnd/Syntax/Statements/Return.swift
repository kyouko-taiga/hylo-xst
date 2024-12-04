import Archivist

/// A return statement.
public struct Return: Statement {

  /// The introducer of this statement.
  public let introducer: Token

  /// The return value, if any.
  public let value: ExpressionIdentity?

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    if let v = value {
      return "return \(program.show(v))"
    } else {
      return "return"
    }
  }

}

extension Return: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.introducer = try archive.read(Token.self, in: &context)
    self.value = try archive.read(ExpressionIdentity?.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(introducer)
    try archive.write(value, in: &context)
    try archive.write(site, in: &context)
  }

}

