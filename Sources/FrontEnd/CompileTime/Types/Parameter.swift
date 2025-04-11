import Archivist

/// A parameter of a callable abstraction.
@Archivable
public struct Parameter: Hashable, Sendable {

  /// The declaration of the parameter if it is not synthetic.
  public let declaration: ParameterDeclaration.ID?

  /// The label of the parameter.
  public let label: String?

  /// The capabilities of the parameter on its argument.
  public let access: AccessEffect

  /// The type of the values that can be passed to the parameter.
  public let type: AnyTypeIdentity

  /// `true` if arguments to the parameter can be passed implicitly.
  public let isImplicit: Bool

  /// Creates an instance with the given properties.
  public init(
    declaration: ParameterDeclaration.ID?,
    label: String?,
    access: AccessEffect,
    type: AnyTypeIdentity,
    isImplicit: Bool
  ) {
    self.declaration = declaration
    self.label = label
    self.access = access
    self.type = type
    self.isImplicit = isImplicit
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> Parameter {
    let t = store.map(type, transform)
    return .init(
      declaration: declaration, label: label, access: access, type: t, isImplicit: isImplicit)
  }

}

extension Parameter: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let t = printer.show(type)
    return if let l = label { "\(l): \(access) \(t)" } else { t }
  }

}
