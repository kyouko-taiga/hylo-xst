import Archivist

/// The declaration of a constraint in a context clause.
public struct UsingDeclaration: Declaration {

  /// The type of the witness represented by this declaration.
  public let witness: ExpressionIdentity

  /// The site from which `self` was parsed.
  public let site: SourceSpan

}

extension UsingDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    printer.show(witness)
  }

}

extension UsingDeclaration: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.witness = try archive.read(ExpressionIdentity.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(witness, in: &context)
    try archive.write(site, in: &context)
  }

}
