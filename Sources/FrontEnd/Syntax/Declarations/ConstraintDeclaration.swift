import Archivist

/// The declaration of a constraint in a context clause.
public struct UsingDeclaration: Declaration {

  /// A constraint operator.
  public enum Operator: UInt8 {

    /// A conformance constraint.
    case conformance

    /// An equality constraint.
    case equality

  }

  /// The left-hand side of the constraint.
  public let lhs: ExpressionIdentity

  /// The right-hand side of the constraint.
  public let rhs: ExpressionIdentity

  /// The semantics of the constraint, which is `.colon` for conformance or `.equal`. for equality.
  public let semantics: Parsed<Operator>

  /// The site from which `self` was parsed.
  public let site: SourceSpan

}

extension UsingDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let s = (semantics.value == .conformance) ? ":" : "=="
    return "\(printer.show(lhs)) \(s) \(printer.show(rhs))"
  }

}

extension UsingDeclaration: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.lhs = try archive.read(ExpressionIdentity.self, in: &context)
    self.rhs = try archive.read(ExpressionIdentity.self, in: &context)
    self.semantics = try archive.read(Parsed<Operator>.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(lhs, in: &context)
    try archive.write(rhs, in: &context)
    try archive.write(semantics, in: &context)
    try archive.write(site, in: &context)
  }

}

extension UsingDeclaration.Operator: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self = try archive.read(rawValueOf: Self.self, in: &context)
      .unwrapOrThrow(ArchiveError.invalidInput)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(rawValueOf: self)
  }

}
