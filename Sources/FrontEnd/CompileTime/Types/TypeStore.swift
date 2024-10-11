import MoreCollections

/// A collection of types.
public struct TypeStore {

  /// The index of a type in a store.
  public typealias Index = Int

  /// The types contained in this store.
  private var types: StableSet<AnyTypeTree>

  /// Creates an empty instance.
  public init() {
    self.types = []
  }

  /// Inserts `t` in `self` it isn't already present and returns the unique identity of a tree that
  /// is equal to `t`.
  public mutating func demand<T: TypeTree>(_ t: T) -> T.ID {
    switch t {
    case is ErrorType:
      return .init(rawValue: AnyTypeIdentity.error.rawValue)
    case let u as Tuple where u.elements.isEmpty:
      return .init(rawValue: AnyTypeIdentity.void.rawValue)
    case let u as Union where u.elements.isEmpty:
      return .init(rawValue: AnyTypeIdentity.never.rawValue)
    default:
      let i = types.insert(.init(t)).position
      assert(i < (1 << 55), "too many types")  // 8 bits are reserved for the properties.
      return .init(rawValue: .init(offset: i, properties: t.properties))
    }
  }

  /// Returns `t` if it identifies a tree of type `U`; otherwise, returns `nil`.
  public func cast<T: TypeIdentity, U: TypeTree>(_ n: T, to: U.Type) -> U.ID? {
    if type(of: self[n]) == U.self {
      return .init(rawValue: n.rawValue)
    } else {
      return nil
    }
  }

  /// Returns `t` assuming it identifies a tree of type `U`.
  public func castUnchecked<T: TypeIdentity, U: TypeTree>(_ n: T, to: U.Type = U.self) -> U.ID {
    assert(type(of: self[n]) == U.self)
    return .init(rawValue: n.rawValue)
  }

  /// Projects the type identified by `n`.
  public subscript<T: TypeTree>(n: T.ID) -> T {
    self[n.rawValue] as! T
  }

  /// Projects the type identified by `n`.
  public subscript<T: TypeIdentity>(n: T) -> any TypeTree {
    _read { yield self[n.rawValue] }
  }

  /// Projects the type identified by `n`.
  internal subscript(n: RawTypeIdentity) -> any TypeTree {
    _read {
      switch n.offset {
      case AnyTypeIdentity.error.rawValue.offset:
        yield ErrorType()
      case AnyTypeIdentity.void.rawValue.offset:
        yield Tuple(elements: [])
      case AnyTypeIdentity.never.rawValue.offset:
        yield Union(elements: [])
      case let n:
        yield types[n].wrapped
      }
    }
  }

}
