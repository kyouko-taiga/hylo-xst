import Archivist
import Utilities

/// The expression of a sum type.
@Archivable
public struct SumTypeExpression: Expression {

  /// The elements of the literal.
  public let elements: [ExpressionIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(elements: [ExpressionIdentity], site: SourceSpan) {
    self.elements = elements
    self.site = site
  }

}

extension SumTypeExpression: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let es = elements.map({ (e) in printer.show(e) })
    return "(\(list: es, joinedBy: " (+) "))"
  }

}
