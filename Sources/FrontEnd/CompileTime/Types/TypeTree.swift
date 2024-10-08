/// The tree representation of a Hylo type.
public protocol TypeTree: Hashable {
  
  /// Properties about `self` and its children, which are types in `program`.
  var properties: ValueProperties { get }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  func show(readingChildrenFrom program: Program) -> String

}

extension TypeTree {

  /// The identity of an instance of `Self`.
  public typealias ID = ConcreteTypeIdentity<Self>

  /// Returns `true` iff `self` has the same tree representation as `other`.
  public func equals(_ other: any TypeTree) -> Bool {
    self == other as? Self
  }

}
