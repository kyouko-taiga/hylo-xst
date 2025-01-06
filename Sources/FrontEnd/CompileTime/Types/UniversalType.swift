/// The type of a type lambda.
public struct UniversalType: TypeTree {

  /// The variables introduced by the quantifier.
  public let parameters: [TypeParameter.ID]

  /// The type under the quantifier.
  public let body: AnyTypeIdentity

  /// Properties about `self`.
  public var properties: ValueProperties {
    parameters.reduce(body.properties, { (a, i) in a.union(i.properties) })
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> UniversalType {
    .init(parameters: parameters, body: store.map(body, transform))
  }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    program.format("<%T*> %T", [parameters.map(\.erased), body])
  }

}
