import Archivist

/// The expression of a conversion.
public struct Coercion: Expression {

  /// A coercion operator.
  public enum Operator: UInt8 {

    /// A guaranteed conversion into a type that can represent the source.
    case up

    /// A forced conversion unto a type that may represent the source.
    case down

    /// A built-in conversion to a pointer.
    case pointer

  }

  /// The value being converted.
  public let source: ExpressionIdentity

  /// The type to which the value is converted.
  public let target: ExpressionIdentity

  /// The semantics of the coercion.
  public let semantics: Operator

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    "\(program.show(source)) \(semantics) \(program.show(target))"
  }

}

extension Coercion: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.source = try archive.read(ExpressionIdentity.self, in: &context)
    self.target = try archive.read(ExpressionIdentity.self, in: &context)
    self.semantics = try archive.read(Operator.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(source, in: &context)
    try archive.write(target, in: &context)
    try archive.write(semantics, in: &context)
    try archive.write(site, in: &context)
  }

}

extension Coercion.Operator: LosslessStringConvertible {

  public init?<T: StringProtocol>(_ description: T) {
    switch description {
    case "as": self = .up
    case "as!": self = .down
    case "as*": self = .pointer
    default: return nil
    }
  }

  public var description: String {
    switch self {
    case .up: return "as"
    case .down: return "as!"
    case .pointer: return "as*"
    }
  }

}

extension Coercion.Operator: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self = try archive.read(rawValueOf: Self.self, in: &context)
      .unwrapOrThrow(ArchiveError.invalidInput)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(rawValueOf: self)
  }

}
