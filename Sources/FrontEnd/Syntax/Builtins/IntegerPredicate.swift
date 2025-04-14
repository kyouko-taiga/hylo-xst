import Archivist

/// The predicate of an integer comparison.
public enum IntegerPredicate: String, Hashable, Sendable {

  /// Values are equal.
  case eq

  /// Values are not equal.
  case ne

  /// LHS is greater than RHS, by unsigned comparison.
  case ugt

  /// LHS is greater than or equal to RHS, by unsigned comparison.
  case uge

  /// LHS is less than RHS, by unsigned comparison.
  case ult

  /// LHS is less than or equal to RHS, by unsigned comparison.
  case ule

  /// LHS is less than RHS, by signed comparison.
  case slt

  /// LHS is greater than or equal to RHS, by signed comparison.
  case sge

  /// LHS is greater than RHS, by signed comparison.
  case sgt

  /// LHS is less than or equal to RHS, by signed comparison.
  case sle

}

extension IntegerPredicate: Archivable {

  public init<A>(from archive: inout ReadableArchive<A>, in context: inout Any) throws {
    self = try archive.readOrThrow(rawValueOf: IntegerPredicate.self, in: &context)
  }

  public func write<A>(to archive: inout WriteableArchive<A>, in context: inout Any) throws {
    try archive.write(rawValueOf: self, in: &context)
  }

}

extension IntegerPredicate: LosslessStringConvertible {

  public init?(_ description: String) {
    self.init(rawValue: description)
  }

  public var description: String { self.rawValue }

}
