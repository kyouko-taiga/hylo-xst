/// The selection of the associated type of some type.
public struct AssociatedType: TypeTree {

  /// The declaration of the type.
  public let declaration: AssociatedTypeDeclaration.ID

  /// The qualification of the type.
  public let qualification: WitnessExpression

  /// Properties about `self` and its children.
  public var properties: ValueProperties {
    qualification.type.properties
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> AssociatedType {
    .init(declaration: declaration, qualification: store.map(qualification, transform))
  }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    let (c, t) = program.types.castToTraitApplication(qualification.type)!
    let m = program[program.types[c].declaration].identifier.value
    let n = program[declaration].identifier.value
    return program.format("(%T::\(m)).\(n)", [t])
  }

}
