import Archivist

/// The expression of the type of an equality witness.
public struct EqualityWitnessExpression: Expression {

  /// The left-hand side of the equality.
  public let lhs: ExpressionIdentity

  /// The right-hand side of the equality.
  public let rhs: ExpressionIdentity

  /// The site from which `self` was parsed.
  public let site: SourceSpan

}

extension EqualityWitnessExpression: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "Coercible<\(printer.show(lhs)), \(printer.show(rhs))>"
  }

}

extension EqualityWitnessExpression: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.lhs = try archive.read(ExpressionIdentity.self, in: &context)
    self.rhs = try archive.read(ExpressionIdentity.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(lhs, in: &context)
    try archive.write(rhs, in: &context)
    try archive.write(site, in: &context)
  }

}
