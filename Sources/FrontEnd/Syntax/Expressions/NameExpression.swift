import Archivist

/// A reference to an entity.
public struct NameExpression: Expression {

  /// The qualification of a name.
  public enum Qualification: Equatable {

    /// Unqualified, as in `bar`.
    case none

    /// Implicit, as the `.` in `.bar`; the whole name denotes a static member.
    case implicit

    /// Explicit, as `foo.` in `foo.bar` or `.foo.` in `.foo.bar`.
    case explicit(ExpressionIdentity)

  }

  /// The qualification of the referred entity.
  public let qualification: Qualification

  /// The name of the referred entity.
  public let name: Parsed<Name>

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    switch qualification {
    case .none:
      return name.description
    case .implicit:
      return "." + name.description
    case .explicit(let e):
      return program.show(e) + "." + name.description
    }
  }

}

extension NameExpression: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.qualification = try archive.read(Qualification.self, in: &context)
    self.name = try archive.read(Parsed<Name>.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(qualification, in: &context)
    try archive.write(name, in: &context)
    try archive.write(site, in: &context)
  }

}

extension NameExpression.Qualification: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    switch try archive.readByte() {
    case 0: self = .none
    case 1: self = .implicit
    case 2: self = .explicit(try archive.read(ExpressionIdentity.self, in: &context))
    default:
      throw ArchiveError.invalidInput
    }
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    switch self {
    case .none:
      archive.write(byte: 0)
    case .implicit:
      archive.write(byte: 1)
    case .explicit(let e):
      archive.write(byte: 2)
      try archive.write(e, in: &context)
    }
  }

}
