import Archivist
import Utilities

/// The introduction of a conformance into the implicit scope.
public struct ModelDeclaration/*: Declaration*/ {

  /// The introducer of this declaration.
  public let introducer: Token

  /// The type for which the conformance is declared.
  public let subject: ExpressionIdentity

  /// The trait for which the conformance is declared.
  public let concept: ExpressionIdentity

  /// The site from which `self` was parsed.
  public var site: SourceSpan

}
