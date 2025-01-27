/// A type alias.
public struct TypeAlias: TypeTree {

  /// The declaration introducing this type.
  public let declaration: TypeAliasDeclaration.ID

  /// The aliased type.
  public let aliasee: AnyTypeIdentity

  /// Properties about `self`.
  public var properties: ValueProperties {
    .hasAliases
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> TypeAlias {
    .init(declaration: declaration, aliasee: store.map(aliasee, transform))
  }

}

extension TypeAlias: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    printer.program[declaration].identifier.value
  }

}
