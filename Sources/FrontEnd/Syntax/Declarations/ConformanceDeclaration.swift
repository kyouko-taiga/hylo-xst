import Archivist

/// The declaration of a conformance of a type to a trait.
public struct ConformanceDeclaration: Declaration, Scope {

  /// The introducer of this declaration.
  public let introducer: Token

  /// The type for which the conformance is declared.
  public let extendee: ExpressionIdentity

  /// The trait to which the conformance is declared.
  public let concept: ExpressionIdentity

  /// The members of the declaration.
  public let members: [DeclarationIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    let e = program.show(extendee)
    let c = program.show(concept)
    let ms = members.map(program.show(_:)).lazy
      .map(\.indented)
      .joined(separator: "\n")

    return """
    conformance \(e): \(c) {
    \(ms)
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
