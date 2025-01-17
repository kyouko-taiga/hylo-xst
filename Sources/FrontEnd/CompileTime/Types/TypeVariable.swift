/// A unification variable in a type tree.
public struct TypeVariable: TypeTree {

  /// The identifier of the variable.
  public let identifier: Int

  /// Properties about `self`.
  public var properties: ValueProperties {
    .hasVariable
  }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    "%\(String(identifier, radix: 36))"
  }

}
