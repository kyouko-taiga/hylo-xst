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

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> AssociatedType {
    .init(declaration: declaration, qualification: store.map(qualification, transform))
  }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    let concept = program.parent(containing: declaration, as: TraitDeclaration.self)!
    let l = program[concept].identifier.value
    let q = program.show(qualification)
    let n = program[declaration].identifier.value
    return "\(q)::\(l).\(n)"
  }

}
