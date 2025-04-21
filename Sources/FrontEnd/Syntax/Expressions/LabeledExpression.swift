import Archivist

/// An expression with an optional label.
@Archivable
public struct LabeledExpression: Hashable, Sendable {

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
