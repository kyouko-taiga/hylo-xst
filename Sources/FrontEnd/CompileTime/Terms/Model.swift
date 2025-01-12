import OrderedCollections

/// A witness of a type's conformance to a trait.
public enum Model {

  /// A concrete model.
  ///
  /// - Parameters:
  ///   - type: The type of the term.
  ///   - implementations: A table from concept requirement to its implementation.
  case concrete(type: TypeApplication.ID, implementations: Implementations)

  /// An asbtract model.
  case abstract(type: TypeApplication.ID)

  /// Creates a concrete model with the given properties.
  public init(_ type: TypeApplication.ID, implementations: Implementations) {
    self = .concrete(type: type, implementations: implementations)
  }

}

extension Model {

  /// The type a table mapping concept requirements to their implementations.
  public typealias Implementations = OrderedDictionary<DeclarationIdentity, Implementation>

  /// The implementation of a concept requirement.
  public enum Implementation: Hashable {

    /// A synthesized implementation.
    case synthetic

    /// An explicit implementation, written in sources.
    case explicit(DeclarationReference, AnyTypeIdentity)

    /// The type of the implementation.
    public var type: AnyTypeIdentity {
      switch self {
      case .synthetic:
        return .error
      case .explicit(_, let t):
        return t
      }
    }

  }

}

extension Model: Term {

  /// The type of the term.
  public var type: AnyTypeIdentity {
    switch self {
    case .concrete(let t, _):
      return t.erased
    case .abstract(let t):
      return t.erased
    }
  }

  /// Properties about `self`.
  public var properties: ValueProperties {
    .init()
  }

}
