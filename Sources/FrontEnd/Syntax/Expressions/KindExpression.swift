import Archivist

/// The expression of a kind.
@Archivable
public struct KindExpression: Expression {

  /// The value of a kind expression.
  @Archivable
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

  /// Creates an instance with the given properties.
  public init(value: Value, site: SourceSpan) {
    self.value = value
    self.site = site
  }

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
