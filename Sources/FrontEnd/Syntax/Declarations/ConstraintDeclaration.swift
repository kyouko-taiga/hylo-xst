import Archivist

/// The declaration of a constraint in a context clause.
public enum ConstraintDeclaration: Equatable {

  /// A parameter accepting a witness `extendee`' conformance to `concept`.
  case conformance(extendee: ExpressionIdentity, concept: ExpressionIdentity)

}

extension ConstraintDeclaration: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    switch try archive.readByte() {
    case 0:
      let t = try archive.read(ExpressionIdentity.self, in: &context)
      let u = try archive.read(ExpressionIdentity.self, in: &context)
      self = .conformance(extendee: t, concept: u)
    default:
      throw ArchiveError.invalidInput
    }
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    switch self {
    case .conformance(let t, let u):
      archive.write(byte: 0)
      try archive.write(t, in: &context)
      try archive.write(u, in: &context)
    }
  }

}

extension Program {

  /// Returns a source-like representation of `d`.
  public func show(_ d: ConstraintDeclaration) -> String {
    switch d {
    case .conformance(let t, let u):
      return "\(show(t)): \(show(u))"
    }
  }

}
