import Archivist

/// The result of overflow during mathematical operations.
public enum OverflowBehavior: UInt8, Sendable {

  /// Overflow is ignored.
  ///
  /// This value is the default, and is thus omitted from `Builtin` function names
  /// (e.g. `Builtin.add_i32`).
  case ignore

  /// The result is a poison value should unsigned overflow occur.
  case nuw

  /// The result is a poison value should signed overflow occur.
  case nsw

}

extension OverflowBehavior: Archivable {

  public init<A>(from archive: inout ReadableArchive<A>, in context: inout Any) throws {
    self = try archive.readOrThrow(rawValueOf: OverflowBehavior.self, in: &context)
  }

  public func write<A>(to archive: inout WriteableArchive<A>, in context: inout Any) throws {
    try archive.write(rawValueOf: self, in: &context)
  }

}
