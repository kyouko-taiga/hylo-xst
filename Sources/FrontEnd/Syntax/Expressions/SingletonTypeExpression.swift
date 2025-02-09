import Archivist
import Utilities

/// The expression of a singleton type.
public struct SingletonTypeExpression: Expression {

  /// The expression of the values having the described by `self`.
  public let expression: ExpressionIdentity

  /// The site from which `self` was parsed.
  public let site: SourceSpan

}

extension SingletonTypeExpression: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "#exactly(\(printer.show(expression)))"
  }

}

extension SingletonTypeExpression: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.expression = try archive.read(ExpressionIdentity.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(expression, in: &context)
    try archive.write(site, in: &context)
  }

}
