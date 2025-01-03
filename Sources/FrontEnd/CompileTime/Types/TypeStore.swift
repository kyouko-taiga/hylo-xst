import MoreCollections
import Utilities

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

  /// Inserts `t` in `self` it isn't already present and returns the identity of an equal tree.
  public mutating func demand<T: TypeTree>(_ t: T) -> T.ID {
    .init(uncheckedFrom: demand(any: t))
  }

  /// Inserts `t` in `self` it isn't already present and returns the identity of an equal tree.
  private mutating func demand(any t: any TypeTree) -> AnyTypeIdentity {
    switch t {
    case is ErrorType:
      return AnyTypeIdentity.error
    case let u as Tuple where u.elements.isEmpty:
      return AnyTypeIdentity.void
    case let u as Union where u.elements.isEmpty:
      return AnyTypeIdentity.never
    case let u as TypeVariable:
      return AnyTypeIdentity(variable: u.identifier)
    default:
      let i = types.insert(.init(t)).position
      assert(i < (1 << 55), "too many types")  // 8 bits are reserved for the properties.
      return .init(offset: i, properties: t.properties)
    }
  }

  /// Returns the kind of `n`.
  public func kind<T: TypeIdentity>(of n: T) -> TypeKind {
    .init(type(of: self[n]))
  }

  /// Returns `true` iff `n` identifies the type of an entity callable as a function.
  public func isArrowLike<T: TypeIdentity>(_ n: T) -> Bool {
    switch kind(of: n) {
    case Arrow.self:
      return true
    default:
      return false
    }
  }

  /// Returns `true` iff `n` identifies the type of an entity callable as a subscript.
  public func isSubscriptLike<T: TypeIdentity>(_ n: T) -> Bool {
    return false
  }

  /// Returns `n` if it identifies a tree of type `U`; otherwise, returns `nil`.
  public func cast<T: TypeIdentity, U: TypeTree>(_ n: T, to: U.Type) -> U.ID? {
    if type(of: self[n]) == U.self {
      return .init(uncheckedFrom: n.erased)
    } else {
      return nil
    }
  }

  /// Returns `n` assuming it identifies a tree of type `U`.
  public func castUnchecked<T: TypeIdentity, U: TypeTree>(_ n: T, to: U.Type = U.self) -> U.ID {
    assert(type(of: self[n]) == U.self)
    return .init(uncheckedFrom: n.erased)
  }

  /// Returns `n` if it identifies a trait application; otherwise, returns `nil`.
  public func castToTraitApplication<T: TypeIdentity>(
    _ n: T
  ) -> (concept: Trait.ID, subject: AnyTypeIdentity)? {
    if
      let t = cast(n, to: TypeApplication.self),
      let u = cast(self[t].abstraction, to: Trait.self),
      let v = self[t].arguments.first?.type
    {
      assert(self[t].arguments.count == 1)
      return (concept: u, subject: v)
    } else {
      return nil
    }
  }

  /// Projects the type identified by `n`.
  public subscript<T: TypeIdentity>(n: T) -> any TypeTree {
    _read { yield self[n.erased] }
  }

  /// Projects the type identified by `n`.
  public subscript<T: TypeTree>(n: T.ID) -> T {
    self[n.erased] as! T
  }

  /// Projects the type identified by `n`.
  internal subscript(n: AnyTypeIdentity) -> any TypeTree {
    _read {
      switch n.offset {
      case AnyTypeIdentity.error.offset:
        yield ErrorType()
      case AnyTypeIdentity.void.offset:
        yield Tuple(elements: [])
      case AnyTypeIdentity.never.offset:
        yield Union(elements: [])
      case let i where n.isVariable:
        yield TypeVariable(identifier: Int(UInt64(i) & ((1 << 54) - 1)))
      case let i:
        yield types[i].wrapped
      }
    }
  }

  /// Returns `n` transformed by `transform(_:_:)`.
  public mutating func map(
    _ n: AnyTypeIdentity,
    _ transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> AnyTypeIdentity {
    switch transform(&self, n) {
    case .stepInto(let m):
      return modified(m, by: transform)
    case .stepOver(let m):
      return m
    }
  }

  /// Returns `n` with its parts transformed by `transform(_:_:)`.
  ///
  /// This operation is endomorphic: the result is an instance with the same type as `n`.
  public mutating func modified(
    _ n: AnyTypeIdentity,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> AnyTypeIdentity {
    let t = self[n].modified(in: &self, by: transform)
    return demand(any: t)
  }

  public mutating func substitute(
    in n: AnyTypeIdentity,
    _ substitution: (TypeStore, AnyTypeIdentity) -> AnyTypeIdentity
  ) -> AnyTypeIdentity {
    self.map(n, { (s, t) in .stepInto(substitution(s, t)) })
  }

  /// Returns `n` with all occurrences of `old` substituted for `new`.
  public mutating func substitute(
    _ old: AnyTypeIdentity, for new: AnyTypeIdentity, in n: AnyTypeIdentity
  ) -> AnyTypeIdentity {
    self.map(n, { (s, t) in .stepInto((t == old) ? new : t) })
  }

  public mutating func adapt(_ t: AnyTypeIdentity, to w: Model) -> AnyTypeIdentity {
    t
  }

}

/// The result of a call to a closure passed to `TypeStore.transform(_:)`.
public enum TypeTransformAction {

  case stepInto(AnyTypeIdentity)

  case stepOver(AnyTypeIdentity)

}
