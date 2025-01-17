import Utilities

/// The type of an implicit abstraction.
public struct Implication: TypeTree {

  /// The left-hand side of the implication, which is not empty.
  public let context: [AnyTypeIdentity]

  /// The right-hand side of the implication.
  public let head: AnyTypeIdentity

  /// Creates an instance with the given properties.
  public init(context: [AnyTypeIdentity], head: AnyTypeIdentity) {
    assert(!context.isEmpty)
    self.context = context
    self.head = head
  }

  /// Properties about `self`.
  public var properties: ValueProperties {
    context.reduce(head.properties, { (a, i) in a.union(i.properties) })
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> Implication {
    .init(
      context: context.map({ (t) in store.map(t, transform) }),
      head: store.map(head, transform))
  }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    program.format("%T* ==> %T", [context, head])
  }

}
