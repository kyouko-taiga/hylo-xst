import Utilities

/// The type of a tuple.
public struct Tuple: TypeTree {

  /// An element in a tuple type.
  public struct Element: Hashable {

    /// The label of the element.
    public let label: String?

    /// The type of the element.
    public let type: AnyTypeIdentity

  }

  /// The elements of the tuple.
  public let elements: [Element]

  /// Properties about `self`.
  public var properties: ValueProperties {
    elements.reduce([], { (a, e) in a.union(e.type.properties) })
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
