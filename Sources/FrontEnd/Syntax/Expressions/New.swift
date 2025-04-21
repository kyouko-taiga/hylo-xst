import Archivist

/// The eta-expansion of an initializer, sugared as an expression of the form `q.new`.
@Archivable
public struct New: Expression {

  /// The qualification of the name expression that `self` desugars.
  public let qualification: ExpressionIdentity

  /// The name expression referring to the eta-expanded receiver.
  public let target: NameExpression.ID

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(qualification: ExpressionIdentity, target: NameExpression.ID, site: SourceSpan) {
    self.qualification = qualification
    self.target = target
    self.site = site
  }

}

extension New: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    printer.show(qualification) + ".new"
  }

}
