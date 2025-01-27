import Archivist

/// The application of an abstraction to compile-time arguments.
public struct StaticCall: Expression {

  /// The abstraction being applied.
  public let callee: ExpressionIdentity

  /// The arguments passed to the abstraction.
  public let arguments: [ExpressionIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

}

extension StaticCall: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "\(printer.show(callee))<\(printer.show(arguments))>"
  }

}

extension StaticCall: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.callee = try archive.read(ExpressionIdentity.self, in: &context)
    self.arguments = try archive.read([ExpressionIdentity].self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(callee, in: &context)
    try archive.write(arguments, in: &context)
    try archive.write(site, in: &context)
  }

}
