import Archivist
import Utilities

/// The declaration of a type alias.
public struct TypeAliasDeclaration: TypeDeclaration, Scope {

  /// The introducer of this declaration.
  public let introducer: Token

  /// The name of the declared alias.
  public let identifier: Parsed<String>

  /// The expression of the aliased type.
  public let aliasee: ExpressionIdentity

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    "typealias \(identifier) = \(program.show(aliasee))"
  }

}

extension TypeAliasDeclaration: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.introducer = try archive.read(Token.self, in: &context)
    self.identifier = try archive.read(Parsed<String>.self, in: &context)
    self.aliasee = try archive.read(ExpressionIdentity.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(introducer, in: &context)
    try archive.write(identifier, in: &context)
    try archive.write(aliasee, in: &context)
    try archive.write(site, in: &context)
  }

}
