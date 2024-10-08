/// The selection of the associated type of some type.
public struct AssociatedType: TypeTree {

  /// The declaration of the type.
  public let declaration: AssociatedTypeDeclaration.ID

  /// The qualification of the type.
  public let qualification: AnyTypeIdentity

  /// Properties about `self` and its children.
  public var properties: ValueProperties {
    qualification.properties
  }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    let q = program.show(qualification)
    let n = program[declaration].identifier.value
    return "\(q).\(n)"
  }

}
