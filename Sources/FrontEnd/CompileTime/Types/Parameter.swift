/// A parameter of a callable abstraction.
public struct Parameter: Hashable {

  /// The declaration of the parameter if it is not synthetic.
  public let declaration: ParameterDeclaration.ID?

  /// The label of the parameter.
  public let label: String?

  /// The type of the parameter.
  public let type: AnyTypeIdentity

  /// `true` if arguments to the parameter can be passed implicitly.
  public let isImplicit: Bool

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> Parameter {
    let t = store.map(type, transform)
    return .init(declaration: declaration, label: label, type: t, isImplicit: isImplicit)
  }

}

extension Program {

  /// Returns a source-like representation of `p`.
  public func show(_ p: Parameter) -> String {
    let t = show(p.type)
    return if let l = p.label { "\(l): \(t)" } else { t }
  }

}
