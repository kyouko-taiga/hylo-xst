import MoreCollections
import Utilities

/// A collection of types.
public struct TypeStore {

  /// The index of a type in a store.
  public typealias Index = Int

  /// A policy for substituting variables during reification.
  public enum SubstitutionPolicy {

    /// Free variables are substituted by errors.
    case substitutedByError

    /// Free variables are kept.
    case kept

  }

  /// The types contained in this store.
  private var types: StableSet<AnyTypeTree>

  /// The identifier of the next fresh variable.
  private var nextFreshIdentifier: Int

  /// Creates an empty instance.
  public init() {
    self.types = []
    self.nextFreshIdentifier = 0
  }

  /// Returns the identity of a fresh type variable.
  public mutating func fresh() -> TypeVariable.ID {
    defer { nextFreshIdentifier += 1 }
    return .init(uncheckedFrom: AnyTypeIdentity(variable: nextFreshIdentifier))
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

  /// Returns the tag of `n`.
  public func tag<T: TypeIdentity>(of n: T) -> TypeTag {
    .init(type(of: self[n]))
  }

  /// Returns `true` iff `n` identifies the type of an entity callable as a function.
  public func isArrowLike<T: TypeIdentity>(_ n: T) -> Bool {
    switch tag(of: n) {
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

  /// Returns `n` sans context clause.
  public func head(_ n: AnyTypeIdentity) -> AnyTypeIdentity {
    switch self[n] {
    case let i as Implication:
      return head(i.head)
    case let u as UniversalType:
      return head(u.body)
    default:
      return n
    }
  }

  /// Returns the head and context clause of `n`.
  public func bodyAndContext(
    _ n: AnyTypeIdentity
  ) -> (body: AnyTypeIdentity, context: ContextClause) {
    let p: [GenericParameter.ID]
    let b: AnyTypeIdentity

    if let u = self[n] as? UniversalType {
      p = u.parameters
      b = u.body
    } else {
      p = []
      b = n
    }

    if let i = self[b] as? Implication {
      return (i.head, .init(parameters: p, usings: i.context))
    } else {
      return (b, .init(parameters: p, usings: []))
    }
  }

  /// Returns `t` as the head of a universal type and/or implication introducing `c`.
  public mutating func introduce(_ c: ContextClause, into n: AnyTypeIdentity) -> AnyTypeIdentity {
    // Fast path: the clause is empty.
    if c.isEmpty { return n }

    // Slow path: introduce parameters.
    var result = n
    if !c.usings.isEmpty {
      result = demand(Implication(context: c.usings, head: result)).erased
    }
    if !c.parameters.isEmpty {
      result = demand(UniversalType(parameters: c.parameters, body: result)).erased
    }
    return result
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

  /// Returns the value at `p` on the type identified by `n` if that type is an instance of `T`.
  /// Otherwise, returns `nil`.
  public func select<T: TypeTree, U>(_ p: KeyPath<T, U>, on n: AnyTypeIdentity) -> U? {
    if let t = self[n] as? T {
      return t[keyPath: p]
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

  /// Returns `n` without any type alias.
  public mutating func dealiased(_ n: AnyTypeIdentity) -> AnyTypeIdentity {
    self.map(n) { (s, t) in
      if let a = s[t] as? TypeAlias {
        return .stepInto(a.aliasee)
      } else if t[.hasAliases] {
        return .stepInto(t)
      } else {
        return .stepOver(t)
      }
    }
  }

  /// Returns `n` with each open variable substituted by either its corresponding value in `subs`
  /// or the application of `substitutionPolicy` if no such substitution exists.
  public mutating func reify(
    _ n: AnyTypeIdentity,
    applying subs: SubstitutionTable,
    withVariables substitutionPolicy: SubstitutionPolicy = .substitutedByError
  ) -> AnyTypeIdentity {
    self.map(n) { (s, t) in
      let u = subs[t]
      if !u.isVariable || substitutionPolicy == .kept {
        return u[.hasVariable] ? .stepInto(u) : .stepOver(u)
      } else {
        return .stepOver(.error)
      }
    }
  }

  /// Returns `r` with its open variables reified by `subs` and `substitutionPolicy`.
  public mutating func reify(
    _ r: DeclarationReference,
    applying subs: SubstitutionTable,
    withVariables substitutionPolicy: SubstitutionPolicy = .substitutedByError
  ) -> DeclarationReference {
    switch r {
    case .predefined, .direct, .member:
      return r
    case .inherited(let w, let d):
      return .inherited(w, d)
    }
  }

  /// Returns `w` with its open variables reified by `subs` and `substitutionPolicy`.
  public mutating func reify(
    _ w: WitnessExpression,
    applying subs: SubstitutionTable,
    withVariables substitutionPolicy: SubstitutionPolicy = .substitutedByError
  ) -> WitnessExpression {
    let t = reify(w.type, applying: subs)

    switch w.value {
    case .reference(let r):
      let u = reify(r, applying: subs, withVariables: substitutionPolicy)
      return .init(value: .reference(u), type: t)

    case .termApplication(let a, let b):
      let u = reify(a, applying: subs, withVariables: substitutionPolicy)
      let v = reify(b, applying: subs, withVariables: substitutionPolicy)
      return .init(value: .termApplication(u, v), type: t)

    case .typeApplication(let a, let b):
      let u = reify(a, applying: subs, withVariables: substitutionPolicy)
      let v = b.map({ (n) in reify(n, applying: subs, withVariables: substitutionPolicy) })
      return .init(value: .typeApplication(u, v), type: t)
    }
  }

  /// Returns `n` with all occurrences of `old` substituted for `new`.
  public mutating func substitute(
    _ old: AnyTypeIdentity, for new: AnyTypeIdentity, in n: AnyTypeIdentity
  ) -> AnyTypeIdentity {
    self.map(n, { (s, t) in .stepInto((t == old) ? new : t) })
  }

  /// Returns `n` with each occurrences of every key in `substitutions` substituted for its
  /// corresponding value.
  public mutating func substitute(
    _ substitutions: [AnyTypeIdentity: AnyTypeIdentity], in n: AnyTypeIdentity
  ) -> AnyTypeIdentity {
    self.map(n) { (s, t) in .stepInto(substitutions[t] ?? t) }
  }

  /// Returns `true` if `t` and `u` can be unified, recording substitutions in `subs`.
  public func unifiable(_ t: AnyTypeIdentity, _ u: AnyTypeIdentity) -> SubstitutionTable? {
    var s = SubstitutionTable()
    if unifiable(t, u, &s) { return s } else { return nil }
  }

  /// Returns `true` iff `lhs` can be unified with `rhs`, recording substitutions in `subs`.
  private func unifiable(
    _ t: Value, _ u: Value, _ subs: inout SubstitutionTable
  ) -> Bool {
    if let a = t.type, let b = u.type {
      return unifiable(a, b, &subs)
    } else {
      return t == u
    }
  }

  /// Returns `true` iff `lhs` can be unified with `rhs`, recording substitutions in `subs`.
  private func unifiable(
    _ t: AnyTypeIdentity, _ u: AnyTypeIdentity, _ subs: inout SubstitutionTable
  ) -> Bool {
    let a = subs[t]
    let b = subs[u]

    // The two types are trivially equal?
    if a == b { return true }

    // There are type variables?
    else if a.isVariable {
      subs.assign(b, to: .init(uncheckedFrom: a))
      return true
    } else if b.isVariable {
      subs.assign(a, to: .init(uncheckedFrom: b))
      return true
    }

    /// There are aliases?
    else if let lhs = self[a] as? TypeAlias {
      return unifiable(lhs.aliasee, b, &subs)
    } else if let rhs = self[b] as? TypeAlias {
      return unifiable(a, rhs.aliasee, &subs)
    }

    // The two types have the same shape?
    switch (self[a], self[b]) {
    case (let lhs as Arrow, let rhs as Arrow):
      return unifiable(lhs, rhs, &subs)
    case (let lhs as AssociatedType, let rhs as AssociatedType):
      return unifiable(lhs, rhs, &subs)
    case (_ as BuiltinType, _ as BuiltinType):
      return false
    case (_ as ErrorType, _ as ErrorType):
      return false
    case (_ as GenericParameter, _ as GenericParameter):
      return false
    case (let lhs as Implication, let rhs as Implication):
      return unifiable(lhs, rhs, &subs)
    case (let lhs as Metatype, let rhs as Metatype):
      return unifiable(lhs, rhs, &subs)
    case (let lhs as RemoteType, let rhs as RemoteType):
      return unifiable(lhs, rhs, &subs)
    case (_ as Struct, _ as Struct):
      return false
    case (_ as Trait, _ as Trait):
      return false
    case (let lhs as Tuple, let rhs as Tuple):
      return unifiable(lhs, rhs, &subs)
    case (let lhs as TypeApplication, let rhs as TypeApplication):
      return unifiable(lhs, rhs, &subs)
    case (let lhs as Union, let rhs as Union):
      return unifiable(lhs, rhs, &subs)
    default:
      assert(tag(of: a) != tag(of: b))
      return false
    }
  }

  /// Returns `true` iff `lhs` can be unified with `rhs`, recording substitutions in `subs`.
  private func unifiable(
    _ lhs: Arrow, _ rhs: Arrow, _ subs: inout SubstitutionTable
  ) -> Bool {
    (lhs.effect == rhs.effect) && (lhs.isByName == rhs.isByName)
      && lhs.labels.elementsEqual(rhs.labels)
      && unifiable(lhs.environment, rhs.environment, &subs)
      && unifiable(lhs.inputs, rhs.inputs, &subs, by: unifiable(_:_:subs:))
      && unifiable(lhs.output, rhs.output, &subs)
  }

  /// Returns `true` iff `lhs` can be unified with `rhs`, recording substitutions in `subs`.
  private func unifiable(
    _ lhs: AssociatedType, _ rhs: AssociatedType, _ subs: inout SubstitutionTable
  ) -> Bool {
    unifiable(lhs.qualification, rhs.qualification, &subs)
  }

  /// Returns `true` iff `lhs` can be unified with `rhs`, recording substitutions in `subs`.
  private func unifiable(
    _ lhs: Implication, _ rhs: Implication, _ subs: inout SubstitutionTable
  ) -> Bool {
    unifiable(lhs.context, rhs.context, &subs) && unifiable(lhs.head, rhs.head, &subs)
  }

  /// Returns `true` iff `lhs` can be unified with `rhs`, recording substitutions in `subs`.
  private func unifiable(
    _ lhs: Metatype, _ rhs: Metatype, _ subs: inout SubstitutionTable
  ) -> Bool {
    unifiable(lhs.inhabitant, rhs.inhabitant, &subs)
  }

  /// Returns `true` iff `lhs` can be unified with `rhs`, recording substitutions in `subs`.
  private func unifiable(
    _ lhs: RemoteType, _ rhs: RemoteType, _ subs: inout SubstitutionTable
  ) -> Bool {
    (lhs.access == rhs.access) && unifiable(lhs.projectee, rhs.projectee, &subs)
  }

  /// Returns `true` iff `lhs` can be unified with `rhs`, recording substitutions in `subs`.
  private func unifiable(
    _ lhs: Tuple, _ rhs: Tuple, _ subs: inout SubstitutionTable
  ) -> Bool {
    unifiable(lhs.elements, rhs.elements, &subs, by: unifiable(_:_:subs:))
  }

  /// Returns `true` iff `lhs` can be unified with `rhs`, recording substitutions in `subs`.
  private func unifiable(
    _ lhs: Parameter, _ rhs: Parameter, subs: inout SubstitutionTable
  ) -> Bool {
    (lhs.label == rhs.label) && unifiable(lhs.type, rhs.type, &subs)
  }

  /// Returns `true` iff `lhs` can be unified with `rhs`, recording substitutions in `subs`.
  private func unifiable(
    _ lhs: TypeApplication, _ rhs: TypeApplication, _ subs: inout SubstitutionTable
  ) -> Bool {
    unifiable(lhs.abstraction, rhs.abstraction, &subs)
      && unifiable(lhs.arguments, rhs.arguments, &subs, by: unifiable(_:_:_:))
  }

  /// Returns `true` iff `lhs` can be unified with `rhs`, recording substitutions in `subs`.
  private func unifiable(
    _ lhs: Union, _ rhs: Union, _ subs: inout SubstitutionTable
  ) -> Bool {
    unifiable(lhs.elements, rhs.elements, &subs)
  }

  /// Returns `true` iff `lhs` can be unified with `rhs`, recording substitutions in `subs`.
  private func unifiable(
    _ lhs: Tuple.Element, _ rhs: Tuple.Element, subs: inout SubstitutionTable
  ) -> Bool {
    (lhs.label == rhs.label) && unifiable(lhs.type, rhs.type, &subs)
  }

  /// Returns `true` iff the the pairwise elements of `lhs` and `rhs` are unifiable by `unify`,
  /// recording substitutions in `subs`.
  private func unifiable<T: Sequence>(
    _ lhs: T, _ rhs: T, _ subs: inout SubstitutionTable,
    by unify: (T.Element, T.Element, inout SubstitutionTable) -> Bool
  ) -> Bool {
    var i = lhs.makeIterator()
    var j = rhs.makeIterator()
    while let a = i.next() {
      guard let b = j.next(), unify(a, b, &subs) else { return false }
    }
    return j.next() == nil
  }

  /// Returns `true` iff the the pairwise elements of `lhs` and `rhs` are unifiable, recording
  /// substitutions in `subs`.
  private func unifiable<T: Sequence<AnyTypeIdentity>>(
    _ lhs: T, _ rhs: T, _ subs: inout SubstitutionTable
  ) -> Bool {
    unifiable(lhs, rhs, &subs, by: unifiable(_:_:_:))
  }

}

/// The result of a call to a closure passed to `TypeStore.transform(_:)`.
public enum TypeTransformAction {

  case stepInto(AnyTypeIdentity)

  case stepOver(AnyTypeIdentity)

}
