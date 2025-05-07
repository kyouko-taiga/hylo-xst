import Utilities

/// A tagged union of types.
public struct Sum: TypeTree {

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
  ) -> Sum {
    .init(elements: elements.map({ (e) in store.map(e, transform) }))
  }

}

extension Sum: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let es = elements.map({ (e) in printer.show(e) })
    return es.isEmpty ? "Never" : "{\(list: es, joinedBy: " + ")}"
  }

}
