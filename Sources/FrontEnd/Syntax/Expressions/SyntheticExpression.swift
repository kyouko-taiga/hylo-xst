import Archivist

/// The expression of a value synthesized during elaboration.
public struct SynthethicExpression: Expression {

  /// The value of a synthetic expression.
  public enum Value: Equatable, Sendable {

    /// A witness inferred by implicit resolution.
    case witness(WitnessExpression)

    /// A default argument.
    case defaultArgument(ParameterDeclaration.ID)

  }

  /// The synthesized expression.
  public let value: Value

  /// The site at which the synthesized expression is anchored.
  public let site: SourceSpan

}

extension SynthethicExpression: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch value {
    case .witness(let w):
      return printer.show(w)
    case .defaultArgument(let n):
      return "$default \(printer.show(printer.program[n].default!))"
    }
  }

}

extension SynthethicExpression: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.value = try archive.read(Value.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(value, in: &context)
    try archive.write(site, in: &context)
  }

}

extension SynthethicExpression.Value: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    switch try archive.readByte() {
    case 0:
      self = try .witness(archive.read(WitnessExpression.self, in: &context))
    case 1:
      self = try .defaultArgument(archive.read(ParameterDeclaration.ID.self, in: &context))
    default:
      throw ArchiveError.invalidInput
    }
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    switch self {
    case .witness(let w):
      archive.write(byte: 0)
      try archive.write(w, in: &context)
    case .defaultArgument(let n):
      archive.write(byte: 1)
      try archive.write(n, in: &context)
    }
  }

}
