/// A class.
public struct Class: TypeTree {

  /// The declaration introducing this type.
  public let declaration: ClassDeclaration.ID

  /// Properties about `self`.
  public var properties: ValueProperties {
    .init()
  }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    program[declaration].identifier.value
  }

}
