import Archivist

/// The declaration of a conformance of a type to a trait.
public struct ConformanceDeclaration: TypeExtendingDeclaration {

  /// The introducer of this declaration.
  public let introducer: Token

  /// The compile-time parameters of the conformance.
  public let staticParameters: StaticParameters

  /// The type for which the conformance is declared.
  public let extendee: ExpressionIdentity

  /// The trait to which the conformance is declared.
  public let concept: ExpressionIdentity

  /// The members of the declaration.
  public let members: [DeclarationIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

}

extension ConformanceDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let e = printer.show(extendee)
    let c = printer.show(concept)
    let w = staticParameters.isEmpty ? "" : " \(printer.show(staticParameters))"
    let m = members.map({ (m) in printer.show(m).indented }).joined(separator: "\n")
    return """
    given\(w) \(e): \(c) {
    \(m)
    }
    """
  }

}

extension ConformanceDeclaration: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    fatalError()
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    fatalError()
  }

}
