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

}

extension Implication: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    if let t = context.uniqueElement {
      return "\(printer.show(t)) ==> \(printer.show(head))"
    } else {
      return "(\(printer.show(context))) ==> \(printer.show(head))"
    }
  }

}
