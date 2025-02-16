///// The type of a kind expression.
//public enum Kind: TypeTree {
//
//  /// The kind of proper types (often written `*` in literature).
//  case proper
//
//  /// The kind of a higher-order type constructor.
//  case arrow(AnyTypeIdentity, AnyTypeIdentity)
//
//  /// Properties about `self`.
//  public var properties: ValueProperties {
//    if case .arrow(let a, let b) = self {
//      return a.properties.union(b.properties)
//    } else {
//      return .init()
//    }
//  }
//
//  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
//  public func modified(
//    in store: inout TypeStore,
//    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
//  ) -> Kind {
//    if case .arrow(let a, let b) = self {
//      return .arrow(store.map(a, transform), store.map(b, transform))
//    } else {
//      return self
//    }
//  }
//
//}
//
//extension Kind: Showable {
//
//  /// Returns a textual representation of `self` using `printer`.
//  public func show(using printer: inout TreePrinter) -> String {
//    switch self {
//    case .proper:
//      return "*"
//    case .arrow(let a, let b):
//      return "(\(printer.show(a)) -> \(printer.show(b)))"
//    }
//  }
//
//}

/// The type of a kind expression.
public struct Metakind: TypeTree {

  /// The kind of which `self` is the type.
  public let inhabitant: Kind

  /// Properties about `self`.
  public var properties: ValueProperties {
    .init()
  }

}

extension Metakind: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    inhabitant.description
  }

}
