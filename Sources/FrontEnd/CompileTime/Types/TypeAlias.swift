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

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> TypeAlias {
    .init(declaration: declaration, aliasee: store.map(aliasee, transform))
  }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    "\(program[declaration].identifier)"
  }

}
