import Archivist

/// The declaration of a type extension.
public struct ExtensionDeclaration: TypeExtendingDeclaration {

  /// The introducer of this declaration.
  public let introducer: Token

  /// The compile-time parameters of the extension.
  public let staticParameters: StaticParameters

  /// The type being extended.
  public let extendee: ExpressionIdentity

  /// The members of the extension.
  public let members: [DeclarationIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

}

extension ExtensionDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let e = printer.show(extendee)
    let w = staticParameters.isEmpty ? "" : " \(printer.show(staticParameters))"
    let m = members.map({ (m) in printer.show(m).indented }).joined(separator: "\n")
    return """
    extension\(w) \(e) {
    \(m)
    }
    """
  }

}

extension ExtensionDeclaration: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    fatalError()
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    fatalError()
  }

}
