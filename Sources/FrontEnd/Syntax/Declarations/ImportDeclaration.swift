import Archivist

/// The declaration of a module import.
public struct ImportDeclaration: Declaration {

  /// The introducer of this declaration.
  public let introducer: Token

  /// The identifier of the imported module.
  public let identifier: Parsed<String>

  /// The site from which `self` was parsed.
  public let site: SourceSpan

}

extension ImportDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "import \(identifier)"
  }

}

extension ImportDeclaration: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    let i = try archive.read(Token.self, in: &context)
    let n = try archive.read(Parsed<String>.self, in: &context)
    let s = try archive.read(SourceSpan.self, in: &context)
    self.init(introducer: i, identifier: n, site: s)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(introducer, in: &context)
    try archive.write(identifier, in: &context)
    try archive.write(site, in: &context)
  }

}
