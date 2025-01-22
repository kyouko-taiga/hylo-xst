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

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    let e = program.show(extendee)
    let w = staticParameters.isEmpty ? "" : " \(program.show(staticParameters))"
    let m = members.map(program.show(_:)).lazy
      .map(\.indented)
      .joined(separator: "\n")

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
