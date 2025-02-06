import Archivist

/// The expression of an explicit conversion.
public struct Conversion: Expression {

  /// A conversion operator.
  public enum Operator: UInt8, Sendable {

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

  /// The semantics of the conversion.
  public let semantics: Operator

  /// The site from which `self` was parsed.
  public let site: SourceSpan

}

extension Conversion: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "\(printer.show(source)) \(semantics) \(printer.show(target))"
  }

}

extension Conversion: Archivable {

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

extension Conversion.Operator: LosslessStringConvertible {

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

extension Conversion.Operator: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self = try archive.read(rawValueOf: Self.self, in: &context)
      .unwrapOrThrow(ArchiveError.invalidInput)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(rawValueOf: self)
  }

}
