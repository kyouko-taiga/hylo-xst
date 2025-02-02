import Archivist

/// The eta-expansion of an initializer, sugared as an expression of the form `q.new`.
public struct New: Expression {

  /// The qualification of the name expression that `self` desugars.
  public let qualification: ExpressionIdentity

  /// The name expression referring to the eta-expanded receiver.
  public let target: NameExpression.ID

  /// The site from which `self` was parsed.
  public let site: SourceSpan

}

extension New: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    printer.show(qualification) + ".new"
  }

}

extension New: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.qualification = try archive.read(ExpressionIdentity.self, in: &context)
    self.target = try archive.read(NameExpression.ID.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(qualification, in: &context)
    try archive.write(target, in: &context)
    try archive.write(site, in: &context)
  }

}
