import Archivist

/// The declaration of a structure.
public struct StructDeclaration: TypeDeclaration, Scope {

  /// The modifiers applied to this declaration.
  public let modifiers: [Parsed<DeclarationModifier>]

  /// The introducer of this declaration.
  public let introducer: Token

  /// The name of the declared struct.
  public let identifier: Parsed<String>

  /// The compile-time parameters of the struct.
  public let staticParameters: StaticParameters

  /// The members of the declared struct.
  public let members: [DeclarationIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

}

extension StructDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = ""
    for m in modifiers { result.append("\(m) ") }
    result.append("struct \(identifier)")

    if !staticParameters.isEmpty {
      result.append(printer.show(staticParameters))
    }

    result.append(" {\n")
    for m in members { result.append(printer.show(m).indented + "\n") }
    result.append("}")

    return result
  }

}

extension StructDeclaration: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.modifiers = try archive.read([Parsed<DeclarationModifier>].self, in: &context)
    self.introducer = try archive.read(Token.self, in: &context)
    self.identifier = try archive.read(Parsed<String>.self, in: &context)
    self.staticParameters = try archive.read(StaticParameters.self, in: &context)
    self.members = try archive.read([DeclarationIdentity].self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(modifiers, in: &context)
    try archive.write(introducer, in: &context)
    try archive.write(identifier, in: &context)
    try archive.write(staticParameters, in: &context)
    try archive.write(members, in: &context)
    try archive.write(site, in: &context)
  }

}
