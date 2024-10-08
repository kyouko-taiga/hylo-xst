import Archivist
import Utilities

/// The declaration of a trait.
public struct TraitDeclaration: Declaration & Scope {

  /// The introducer of this declaration.
  public let introducer: Token

  /// The name of the declared trait.
  public let identifier: Parsed<String>

  /// The members of the declared trait.
  public let members: [DeclarationIdentity]

  /// The site from which `self` was parsed.
  public var site: SourceSpan

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    let ms = members.map(program.show(_:)).lazy
      .map(\.indented)
      .joined(separator: "\n")

    return """
    trait \(identifier) {
    \(ms)
    }
    """
  }

}

extension TraitDeclaration: Archivable {
  
  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    let i = try archive.read(Token.self, in: &context)
    let n = try archive.read(Parsed<String>.self, in: &context)
    let m = try archive.read([DeclarationIdentity].self, in: &context)
    let s = try archive.read(SourceSpan.self, in: &context)
    self.init(introducer: i, identifier: n, members: m, site: s)
  }
  
  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(introducer, in: &context)
    try archive.write(identifier, in: &context)
    try archive.write(members, in: &context)
    try archive.write(site, in: &context)
  }

}
