import Archivist

/// The declaration of a structure.
public struct StructDeclaration: TypeDeclaration, Scope {

  /// The introducer of this declaration.
  public let introducer: Token

  /// The name of the declared struct.
  public let identifier: Parsed<String>

  /// The generic parameters of the struct.
  public let parameters: [GenericParameterDeclaration.ID]

  /// The members of the declared struct.
  public let members: [DeclarationIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    let ms = members.map(program.show(_:)).lazy
      .map(\.indented)
      .joined(separator: "\n")

    return """
    struct \(identifier) {
    \(ms)
    }
    """
  }

}

extension StructDeclaration: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.introducer = try archive.read(Token.self, in: &context)
    self.identifier = try archive.read(Parsed<String>.self, in: &context)
    self.parameters = try archive.read([GenericParameterDeclaration.ID].self, in: &context)
    self.members = try archive.read([DeclarationIdentity].self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(introducer, in: &context)
    try archive.write(identifier, in: &context)
    try archive.write(parameters, in: &context)
    try archive.write(members, in: &context)
    try archive.write(site, in: &context)
  }

}
