import Archivist

/// An expression with an optional label.
public struct LabeledExpression: Hashable {

  /// The label of the expression, if any.
  public let label: Parsed<String>?

  /// The expression.
  public let value: ExpressionIdentity

  /// Creates an instance with the given properties.
  public init(label: Parsed<String>?, value: ExpressionIdentity) {
    self.label = label
    self.value = value
  }

}

extension LabeledExpression: LabeledSyntax {

  public typealias Value = ExpressionIdentity

}

extension LabeledExpression: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let v = printer.show(value)
    return if let l = label { "\(l): \(v)" } else { v }
  }

}

extension LabeledExpression: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.label = try archive.read(Parsed<String>.self, in: &context)
    self.value = try archive.read(ExpressionIdentity.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(label, in: &context)
    try archive.write(value, in: &context)
  }

}
