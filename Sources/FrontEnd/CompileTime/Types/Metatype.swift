/// The type of a type.
public struct Metatype: TypeTree {

  /// The type of which `self` is the type.
  public let inhabitant: AnyTypeIdentity

  /// Properties about `self`.
  public var properties: ValueProperties {
    inhabitant.properties
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> Metatype {
    .init(inhabitant: store.map(inhabitant, transform))
  }

}

extension Metatype: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "Metatype<\(printer.show(inhabitant))>"
  }

}
