import Archivist

/// The assignment of a lvalue.
@Archivable
public struct Assignment: Statement {

  /// The lvalue being assigned.
  public let lhs: ExpressionIdentity

  /// The value assigned to the left-hand-side.
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

extension Assignment: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "\(printer.show(lhs)) = \(printer.show(rhs))"
  }

}
