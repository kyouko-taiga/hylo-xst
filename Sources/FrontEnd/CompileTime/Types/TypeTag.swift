/// The type of a node in a type tree.
public struct TypeTag {

  /// The underlying value of `self`.
  public let value: any TypeTree.Type

  /// Creates an instance with the given underlying value.
  public init(_ value: any TypeTree.Type) {
    self.value = value
  }

  /// Returns `true` iff `scrutinee` and `pattern` denote the same node type.
  public static func ~= (pattern: any TypeTree.Type, scrutinee: Self) -> Bool {
    scrutinee == pattern
  }

  /// Returns `true` iff `l` and `r` denote the same node type.
  public static func == (l: Self, r: any TypeTree.Type) -> Bool {
    l.value == r
  }

}

extension TypeTag: Equatable {

  public static func == (l: Self, r: Self) -> Bool {
    l.value == r.value
  }

}

extension TypeTag: Hashable {

  public func hash(into hasher: inout Hasher) {
    hasher.combine(ObjectIdentifier(value))
  }

}

extension TypeTag: CustomStringConvertible {

  public var description: String {
    String(describing: value)
  }

}
