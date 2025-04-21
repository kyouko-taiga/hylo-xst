import Archivist

/// A reference to an entity.
@Archivable
public struct NameExpression: Expression {

  /// The qualification of the referred entity, if any.
  public let qualification: ExpressionIdentity?

  /// The name of the referred entity.
  public let name: Parsed<Name>

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(qualification: ExpressionIdentity?, name: Parsed<Name>, site: SourceSpan) {
    self.qualification = qualification
    self.name = name
    self.site = site
  }

}

extension NameExpression: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    if let q = qualification {
      return printer.show(q) + "." + name.description
    } else {
      return name.description
    }
  }

}
