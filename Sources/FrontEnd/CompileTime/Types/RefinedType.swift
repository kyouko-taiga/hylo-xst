/// A type with a where clause.
public struct RefinedType: TypeTree {

  /// The type to which a where clause is attached.
  public let base: AnyTypeIdentity

  /// The where clause attached to `base`.
  public let refinements: [Int]

  /// Properties about `self`.
  public var properties: ValueProperties {
    base.properties
  }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    return "\(program.show(base))"
  }

}

enum refinement {
  
}
