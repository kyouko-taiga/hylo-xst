import OrderedCollections

/// A witness of a type's conformance to a trait.
public struct Model: Term {

  /// The type a table mapping concept requirements to their implementations.
  public typealias Implementations = OrderedDictionary<DeclarationIdentity, Implementation>

  /// The implementation of a concept requirement.
  public enum Implementation: Hashable {

    /// An explicit implementation, written in sources.
    case explicit(DeclarationReference, AnyTypeIdentity)

    /// A synthesized implementation.
    case synthetic

    /// The type of the implementation.
    public var type: AnyTypeIdentity {
      switch self {
      case .explicit(_, let t):
        return t
      case .synthetic:
        return .error
      }
    }

  }

  /// The type of the term.
  public let type: AnyTypeIdentity

  /// A table from concept requirement to its implementation.
  public let implementations: Implementations

  /// Creates an instance with the given properties.
  public init(_ type: TypeApplication.ID, implementations: Implementations) {
    self.type = type.erased
    self.implementations = implementations
  }

  /// Properties about `self`.
  public var properties: ValueProperties {
    .init()
  }

}
