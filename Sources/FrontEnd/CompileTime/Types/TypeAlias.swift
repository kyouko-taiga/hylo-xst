/// A type alias.
public struct TypeAlias: TypeTree {

  /// The declaration introducing this type.
  public let declaration: TypeAliasDeclaration.ID

  /// The aliased type.
  public let aliasee: AnyTypeIdentity

  /// Properties about `self`.
  public var properties: ValueProperties {
    .notCanonical
  }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    "\(program[declaration].identifier)"
  }

}
