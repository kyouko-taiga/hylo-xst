import Archivist

/// The declaration of a generic parameter.
public struct GenericParameterDeclaration: Declaration {

  /// The identifier of the parameter.
  public let identifier: Parsed<String>

  /// The site from which `self` was parsed.
  public let site: SourceSpan

}

extension GenericParameterDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    identifier.value
  }

}

extension GenericParameterDeclaration: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.identifier = try archive.read(Parsed<String>.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(identifier, in: &context)
    try archive.write(site, in: &context)
  }

}
