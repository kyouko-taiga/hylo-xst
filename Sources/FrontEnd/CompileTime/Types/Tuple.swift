import Utilities

/// The type of a tuple.
public struct Tuple: TypeTree {

  /// An element in a tuple type.
  public struct Element: Hashable {

    /// The label of the element.
    public let label: String?

    /// The type of the element.
    public let type: AnyTypeIdentity

    /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
    public func modified(
      in store: inout TypeStore,
      by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
    ) -> Element {
      .init(label: label, type: store.map(type, transform))
    }

  }

  /// The elements of the tuple.
  public let elements: [Element]

  /// The labels associated with each element.
  public var labels: some Sequence<String?> {
    elements.lazy.map(\.label)
  }

  /// Properties about `self`.
  public var properties: ValueProperties {
    elements.reduce([], { (a, e) in a.union(e.type.properties) })
  }

  /// Returns `true` iff the labels of the elements in `self` are equal to the labels of the
  /// elements in `other`, which are at `path`.
  public func labelsEqual<T: Sequence>(_ other: T, _ path: KeyPath<T.Element, String?>) -> Bool {
    elements.elementsEqual(other, by: { (a, b) in a.label == b[keyPath: path] })
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> Tuple {
    .init(elements: elements.map({ (e) in e.modified(in: &store, by: transform) }))
  }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    elements.isEmpty ? "Void" : "{\(list: elements.map(program.show(_:)))}"
  }

}

extension Program {

  /// Returns a source-like representation of `e`.
  public func show(_ e: Tuple.Element) -> String {
    let t = show(e.type)
    return if let l = e.label { "\(l): \(t)" } else { t }
  }

}
