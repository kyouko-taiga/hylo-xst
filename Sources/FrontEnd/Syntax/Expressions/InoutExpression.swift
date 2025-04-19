import Archivist

/// The expression of a lvalue marked for mutation.
@Archivable
public struct InoutExpression: Expression {

  /// The mutation marker of the expression.
  public let marker: Token

  /// The expression of the lvalue.
  public let lvalue: ExpressionIdentity

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(marker: Token, lvalue: ExpressionIdentity, site: SourceSpan) {
    self.marker = marker
    self.lvalue = lvalue
    self.site = site
  }

}

extension InoutExpression: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "&\(printer.show(lvalue))"
  }

}
