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

  /// Creates an instance with the given name and no qualification
  public init(_ name: Parsed<Name>) {
    self.qualification = nil
    self.name = name
    self.site = name.site
  }

  /// Returns `true` if `self` is an unqualified simple identifier.
  public var isUnqualifiedIdentifier: Bool {
    (qualification == nil) && name.value.isSimple
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
