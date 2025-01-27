import Archivist
import Utilities

/// The declaration of a trait.
public struct TraitDeclaration: TypeDeclaration, Scope {

  /// The introducer of this declaration.
  public let introducer: Token

  /// The name of the declared trait.
  public let identifier: Parsed<String>

  /// The generic parameters of the trait.
  ///
  /// The first element introduces the trait's conformer.
  public let parameters: [GenericParameterDeclaration.ID]

  /// The members of the declared trait.
  public let members: [DeclarationIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// The declaration of the generic parameter referring to conforming types.
  public var conformer: GenericParameterDeclaration.ID {
    parameters[0]
  }

}

extension TraitDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let m = members.map({ (m) in printer.show(m).indented }).joined(separator: "\n")
    return """
    trait \(identifier) {
    \(m)
    }
    """
  }

}

extension TraitDeclaration: Archivable {
  
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
