/// A union of types.
public struct Union: TypeTree {

  /// The elements of the union.
  public let elements: [AnyTypeIdentity]

  /// Properties about `self`.
  public var properties: ValueProperties {
    elements.reduce([], { (a, e) in a.union(e.properties) })
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> Union {
    .init(elements: elements.map({ (e) in store.map(e, transform) }))
  }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    elements.isEmpty ? "Never" : "Union<\(list: elements.map(program.show(_:)))>"
  }

}
