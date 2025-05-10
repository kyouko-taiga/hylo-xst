import Archivist

/// The expression of the type of an equality witness.
@Archivable
public struct EqualityWitnessExpression: Expression {

  /// The left-hand side of the equality.
  public let lhs: ExpressionIdentity

  /// The right-hand side of the equality.
  public let rhs: ExpressionIdentity

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(lhs: ExpressionIdentity, rhs: ExpressionIdentity, site: SourceSpan) {
    self.lhs = lhs
    self.rhs = rhs
    self.site = site
  }

}

extension EqualityWitnessExpression: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "Coercible<\(printer.show(lhs)), \(printer.show(rhs))>"
  }

}
