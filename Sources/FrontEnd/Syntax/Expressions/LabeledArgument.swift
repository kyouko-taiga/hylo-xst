import Archivist

/// A argument with its label.
public struct LabeledArgument: Hashable {

  /// The label of the argument, if any.
  public let label: Parsed<String>?

  /// The value of the argument.
  public let value: ExpressionIdentity

  /// Creates an instance with the given properties.
  public init(label: Parsed<String>?, value: ExpressionIdentity) {
    self.label = label
    self.value = value
  }

}

extension LabeledArgument: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.label = try archive.read(Parsed<String>.self, in: &context)
    self.value = try archive.read(ExpressionIdentity.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(label, in: &context)
    try archive.write(value, in: &context)
  }

}

extension Program {

  /// Returns a source-like representation of `a`.
  public func show(_ a: LabeledArgument) -> String {
    let v = show(a.value)
    return if let l = a.label { "\(l): \(v)" } else { v }
  }

}
