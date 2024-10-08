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
    let i = types.insert(.init(t)).position
    return .init(rawValue: .init(offset: i, properties: t.properties))
  }

  /// Projects the type identified by `n`.
  public subscript<T: TypeTree>(n: T.ID) -> T {
    self[n.rawValue] as! T
  }

  /// Projects the type identified by `n`.
  public subscript<T: TypeIdentity>(n: T) -> any TypeTree {
    _read { yield types[n.rawValue.offset].wrapped }
  }

  /// Projects the type identified by `n`.
  internal subscript(n: RawTypeIdentity) -> any TypeTree {
    _read { yield types[n.offset].wrapped }
  }

}
