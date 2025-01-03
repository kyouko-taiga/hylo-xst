import Utilities

/// A generic type parameter.
public struct TypeParameter: TypeTree {

  /// The declaration of the parameter.
  public let declaration: GenericParameterDeclaration.ID

  /// Properties about `self`.
  public var properties: ValueProperties {
    .init()
  }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    program[declaration].identifier.value
  }

}
