import Archivist

/// The expression of a kind.
public struct KindExpression: Expression {

  /// The value of a kind expression.
  public enum Value: Equatable, Sendable {

    /// The kind of monotypes.
    case proper

    /// The kind of a higher-order type constructor.
    case arrow(KindExpression.ID, KindExpression.ID)

  }

  /// The value of the expression.
  public let value: Value

  /// The site from which `self` was parsed.
  public let site: SourceSpan

}

extension KindExpression: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch value {
    case .proper:
      return "*"
    case .arrow(let a, let b):
      return "(\(printer.show(a)) -> \(printer.show(b)))"
    }
  }

}

extension KindExpression: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.value = try archive.read(KindExpression.Value.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(value, in: &context)
    try archive.write(site, in: &context)
  }

}

extension KindExpression.Value: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    switch try archive.readByte() {
    case 0:
      self = .proper

    case 1:
      let a = try archive.read(KindExpression.ID.self, in: &context)
      let b = try archive.read(KindExpression.ID.self, in: &context)
      self = .arrow(a, b)

    default:
      throw ArchiveError.invalidInput
    }
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    switch self {
    case .proper:
      archive.write(byte: 0)

    case .arrow(let a, let b):
      archive.write(byte: 1)
      try archive.write(a, in: &context)
      try archive.write(b, in: &context)
    }
  }

}
