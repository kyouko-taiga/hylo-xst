/// A struct.
public struct Struct: TypeTree {

  /// The declaration introducing this type.
  public let declaration: StructDeclaration.ID

  /// Properties about `self`.
  public var properties: ValueProperties {
    .init()
  }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    program[declaration].identifier.value
  }

}
