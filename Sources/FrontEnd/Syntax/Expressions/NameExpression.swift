import Archivist

/// A reference to an entity.
public struct NameExpression: Expression {

  /// The qualification of the referred entity, if any.
  public let qualification: ExpressionIdentity?

  /// The name of the referred entity.
  public let name: Parsed<Name>

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    if let q = qualification {
      if program.tag(of: q) == ImplicitQualification.self {
        return "." + name.description
      } else {
        return program.show(q) + "." + name.description
      }
    } else {
      return name.description
    }
  }

}

extension NameExpression: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.qualification = try archive.read(ExpressionIdentity?.self, in: &context)
    self.name = try archive.read(Parsed<Name>.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(qualification, in: &context)
    try archive.write(name, in: &context)
    try archive.write(site, in: &context)
  }

}
