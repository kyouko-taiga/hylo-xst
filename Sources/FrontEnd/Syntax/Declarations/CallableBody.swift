import Archivist

/// The body of a function, lambda, or subscript.
public enum CallableBody: Equatable {

  /// An expression body.
  case expression(ExpressionIdentity)

  /// A block body.
  // case block(BraceStmt.ID)

  /// The identity wrapped by this instance.
  public var identity: AnySyntaxIdentity {
    switch self {
    case .expression(let n):
      return .init(n)
    }
  }

}

extension CallableBody: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    switch try archive.readByte() {
    case 0:
      self = try .expression(archive.read(ExpressionIdentity.self, in: &context))
    default:
      throw ArchiveError.invalidInput
    }
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    switch self {
    case .expression(let n):
      archive.write(byte: 0)
      try archive.write(n, in: &context)
    }
  }

}
