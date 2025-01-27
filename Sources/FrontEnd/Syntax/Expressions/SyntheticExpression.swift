import Archivist

/// The expression of a value synthesized during elaboration.
public struct SynthethicExpression: Expression {

  /// The value of a synthetic expression.
  public enum Value: Equatable {

    /// The receiver an eta-expanded initializer.
    case temporary(AnyTypeIdentity)

    /// A default argument.
    case defaultArgument(ParameterDeclaration.ID)

  }

  /// The synthesized expression.
  public let value: Value

  /// The site at which the synthesized expression is anchored.
  public let site: SourceSpan

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    switch value {
    case .temporary:
      return "$x"
    case .defaultArgument(let n):
      return "$default \(program.show(program[n].default!))"
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
      self = .temporary(.error) // TODO
    case 1:
      self = try .defaultArgument(archive.read(ParameterDeclaration.ID.self, in: &context))
    default:
      throw ArchiveError.invalidInput
    }
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    switch self {
    case .temporary:
      archive.write(byte: 0)
    case .defaultArgument(let n):
      archive.write(byte: 1)
      try archive.write(n, in: &context)
    }
  }

}
