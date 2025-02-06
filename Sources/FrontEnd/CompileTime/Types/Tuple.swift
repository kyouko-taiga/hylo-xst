import Utilities

/// The type of a tuple.
public struct Tuple: TypeTree {

  /// An element in a tuple type.
  public struct Element: Hashable, Sendable {

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

}

extension Tuple: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let es = elements.map({ (e) in printer.show(e) })
    return es.isEmpty ? "Void" : "{\(list: es)}"
  }

}

extension Tuple.Element: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let t = printer.show(type)
    return if let l = label { "\(l): \(t)" } else { t }
  }

}
