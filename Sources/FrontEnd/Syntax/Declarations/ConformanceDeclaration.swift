import Archivist

/// The declaration of a conformance of a type to a trait.
public struct ConformanceDeclaration: TypeExtendingDeclaration {

  /// The introducer of this declaration, unless it is part of a context clause.
  public let introducer: Token?

  /// The parameters of the conformance.
  public let contextParameters: StaticParameters

  /// The type for which the conformance is declared.
  public let extendee: ExpressionIdentity

  /// The trait to which the conformance is declared.
  public let concept: ExpressionIdentity

  /// The members of the declaration.
  public let members: [DeclarationIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// `true` iff this declaration occurs in a context clause.
  public var isAbstract: Bool {
    introducer == nil
  }

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    let e = program.show(extendee)
    let c = program.show(concept)

    if isAbstract {
      assert(contextParameters.isEmpty)
      return "\(e): \(c)"
    } else {
      let w = contextParameters.isEmpty ? "" : " \(program.show(contextParameters))"
      let m = members.map(program.show(_:)).lazy
        .map(\.indented)
        .joined(separator: "\n")

      return """
      given\(w) \(e): \(c) {
      \(m)
      }
      """
    }
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
