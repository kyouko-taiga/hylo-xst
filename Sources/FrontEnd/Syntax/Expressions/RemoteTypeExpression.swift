import Archivist
import Utilities

/// The expression of a remote type.
@Archivable
public struct RemoteTypeExpression: Expression {

  /// The capabilities of the projection.
  public let access: Parsed<AccessEffect>

  /// The type of the projected value.
  public let projectee: ExpressionIdentity

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(access: Parsed<AccessEffect>, projectee: ExpressionIdentity, site: SourceSpan) {
    self.access = access
    self.projectee = projectee
    self.site = site
  }

}

extension RemoteTypeExpression: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "\(access) \(printer.show(projectee))"
  }

}
