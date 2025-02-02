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

  /// Returns `true` iff `n` identifies the type of an equality witness.
  public func isEquality<T: TypeIdentity>(_ n: T) -> Bool {
    tag(of: n) == EqualityWitness.self
  }

  /// Returns `true` iff `n` identifies the type of an entity callable as a function.
  public func isArrowLike<T: TypeIdentity>(_ n: T) -> Bool {
    tag(of: n) == Arrow.self
  }

  /// Returns `true` iff `n` identifies the type of an entity callable as a subscript.
  public func isSubscriptLike<T: TypeIdentity>(_ n: T) -> Bool {
    return false
  }

  /// Returns `true` iff `n` is a universal type or an implication.
  public func hasContext<T: TypeIdentity>(_ n: T) -> Bool {
    (tag(of: n) == UniversalType.self) || (tag(of: n) == Implication.self)
  }

  /// Returns `n` sans context clause.
  public func head(_ n: AnyTypeIdentity) -> AnyTypeIdentity {
    var h = n
    while true {
      switch self[h] {
      case let t as UniversalType:
        h = t.body
      case let t as Implication:
        h = t.body
      default:
        return h
      }
    }
  }

  /// Returns the head and context clause of `n`.
  public func contextAndHead(
    _ n: AnyTypeIdentity
  ) -> (context: ContextClause, body: AnyTypeIdentity) {
    var p: [GenericParameter.ID] = []
    var u: [AnyTypeIdentity] = []
    var h = n

    while true {
      switch self[h] {
      case let t as UniversalType:
        p.append(contentsOf: t.parameters)
        h = t.body
      case let t as Implication:
        u.append(contentsOf: t.usings)
        h = t.body
      default:
        return (.init(parameters: p, usings: u), h)
      }
    }
  }

  /// Returns the implement parameters and head of `n` opened for unification.
  public mutating func open(
    _ n: AnyTypeIdentity
  ) -> (usings: [AnyTypeIdentity], head: AnyTypeIdentity) {
    var u: [AnyTypeIdentity] = []
    var h = n

    while true {
      switch self[h] {
      case let t as UniversalType:
        let a = open(t.parameters)
        h = substitute(a, in: t.body)
      case let t as Implication:
        u.append(contentsOf: t.usings)
        h = t.body
      default:
        return (u, h)
      }
    }
  }

  /// Returns a table mapping each parameter in `ps` to a fresh unification variable.
  public mutating func open(_ ps: [GenericParameter.ID]) -> TypeApplication.Arguments {
    .init(uniqueKeysWithValues: ps.map({ (p) in (p, fresh().erased) }))
  }

  /// Returns `body` as the head of a universal type and/or implication introducing `c`.
  public mutating func introduce(
    _ c: ContextClause, into body: AnyTypeIdentity
  ) -> AnyTypeIdentity {
    let t = introduce(usings: c.usings, into: body)
    let u = introduce(parameters: c.parameters, into: t)
    return u
  }

  /// Returns `body` as the head of an implication having `lhs` on the left-hand side.
  public mutating func introduce(
    usings lhs: [AnyTypeIdentity], into body: AnyTypeIdentity
  ) -> AnyTypeIdentity {
    lhs.isEmpty ? body : demand(Implication(context: lhs, head: body)).erased
  }

  /// Returns `body` as the head of a universal type introducing `ps`.
  public mutating func introduce(
    parameters ps: [GenericParameter.ID], into body: AnyTypeIdentity
  ) -> AnyTypeIdentity {
    ps.isEmpty ? body : demand(UniversalType(parameters: ps, body: body)).erased
  }

  /// Returns `n` without its first requirement.
  public mutating func dropFirstRequirement(_ n: Implication.ID) -> AnyTypeIdentity {
    let i = self[n]
    if i.usings.count == 1 {
      return i.body
    } else {
      return demand(Implication(context: .init(i.usings.dropFirst()), head: i.body)).erased
    }
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

  /// Returns `(P, [A...])` iff `n` has the form `P<A...>`.
  public func seenAsTraitApplication<T: TypeIdentity>(
    _ n: T
  ) -> (concept: Trait.ID, arguments: TypeApplication.Arguments)? {
    if
      let t = cast(n, to: TypeApplication.self),
      let u = cast(self[t].abstraction, to: Trait.self),
      !self[t].arguments.isEmpty
    {
      return (concept: u, arguments: self[t].arguments)
    } else {
      return nil
    }
  }

  /// Returns `([A...], T)` iff `n` has the form `[{self: set T}](A...) -> Void`.
  public func seenAsConstructor<T: TypeIdentity>(
    _ n: T
  ) -> (inputs: [Parameter], output: AnyTypeIdentity)? {
    guard
      let f = self[n] as? Arrow,
      let t = self[f.environment] as? Tuple,
      let e = t.elements.uniqueElement,
      let p = self[e.type] as? RemoteType,
      (e.label == "self") && (p.access == .set) && (f.output == .void)
    else { return nil }
    return (inputs: f.inputs, output: p.projectee)
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

  /// Returns `r` transformed by `transform(_:_:)`.
  public mutating func map(
    _ r: DeclarationReference,
    _ transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> DeclarationReference {
    switch r {
    case .builtin, .direct, .member:
      return r
    case .inherited(let w, let d):
      return .inherited(self.map(w, transform), d)
    }
  }

  /// Returns `w` transformed by `transform(_:_:)`.
  public mutating func map(
    _ w: WitnessExpression,
    _ transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> WitnessExpression {
    let t = self.map(w.type, transform)

    switch w.value {
    case .identity(let e):
      return .init(value: .identity(e), type: t)

    case .abstract:
      return .init(value: .abstract, type: t)

    case .assumed(let i):
      return .init(value: .assumed(i), type: t)

    case .reference(let r):
      let u = self.map(r, transform)
      return .init(value: .reference(u), type: t)

    case .termApplication(let a, let b):
      let u = self.map(a, transform)
      let v = self.map(b, transform)
      return .init(value: .termApplication(u, v), type: t)

    case .typeApplication(let a, let b):
      let u = self.map(a, transform)
      let v = b.mapValues({ (n) in self.map(n, transform) })
      return .init(value: .typeApplication(u, v), type: t)

    case .nested(let a):
      let u = self.map(a, transform)
      return .init(value: .nested(u), type: t)
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
    withVariables substitutionPolicy: SubstitutionPolicy
  ) -> DeclarationReference {
    self.map(r) { (s, t) in
      .stepOver(s.reify(t, applying: subs, withVariables: substitutionPolicy))
    }
  }

  /// Returns `w` with its open variables reified by `subs` and `substitutionPolicy`.
  public mutating func reify(
    _ w: WitnessExpression,
    applying subs: SubstitutionTable,
    withVariables substitutionPolicy: SubstitutionPolicy
  ) -> WitnessExpression {
    self.map(w) { (s, t) in
      .stepOver(s.reify(t, applying: subs, withVariables: substitutionPolicy))
    }
  }

  /// Returns `n` with all occurrences of `old` substituted for `new`.
  public mutating func substitute(
    _ old: AnyTypeIdentity, for new: AnyTypeIdentity, in n: AnyTypeIdentity
  ) -> AnyTypeIdentity {
    self.map(n) { (s, t) in
      t == old ? .stepOver(new) : .stepInto(t)
    }
  }

  /// Returns `n` with the keys in `substitutions` substituted for their corresponding values.
  public mutating func substitute(
    _ substitutions: [AnyTypeIdentity: AnyTypeIdentity], in n: AnyTypeIdentity
  ) -> AnyTypeIdentity {
    self.map(n) { (s, t) in
      if let u = substitutions[t] { .stepOver(u) } else { .stepInto(t) }
    }
  }

  /// Returns `n` with the keys in `substitutions` substituted for their corresponding values.
  public mutating func substitute(
    _ substitutions: TypeApplication.Arguments, in n: AnyTypeIdentity
  ) -> AnyTypeIdentity {
    self.map(n) { (s, t) in
      // The uncheked cast is okay because type of an identity is irrelevant to `Hashable`.
      if let u = substitutions[.init(uncheckedFrom: t)] { .stepOver(u) } else { .stepInto(t) }
    }
  }

  /// Returns `n` with unification variables substituted for an error.
  public mutating func substituteVariableForError(in n: AnyTypeIdentity) -> AnyTypeIdentity {
    self.map(n) { (s, t) in
      if t.isVariable {
        return .stepOver(.error)
      } else {
        return t[.hasVariable] ? .stepInto(t) : .stepOver(t)
      }
    }
  }

  /// Returns a substitution table that makes `lhs` and `rhs` equal modulo substitution of their
  /// open variables.
  public func unifiable(_ lhs: AnyTypeIdentity, _ rhs: AnyTypeIdentity) -> SubstitutionTable? {
    var s = SubstitutionTable()
    if unifiable(lhs, rhs, extending: &s, handlingCoercionsWith: { (_, _) in false }) {
      return s
    } else {
      return nil
    }
  }

  /// Returns `true` if `lhs` and `rhs` can be made equal, recording substitutions of unification
  /// variables in `subs` and calling `areCoercible` to resolve non-syntactically equalities.
  public func unifiable(
    _ lhs: AnyTypeIdentity, _ rhs: AnyTypeIdentity, extending subs: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    let a = subs[lhs]
    let b = subs[rhs]

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
    else if let t = self[a] as? TypeAlias {
      return unifiable(t.aliasee, b, extending: &subs, handlingCoercionsWith: areCoercible)
    } else if let u = self[b] as? TypeAlias {
      return unifiable(a, u.aliasee, extending: &subs, handlingCoercionsWith: areCoercible)
    }

    // The two types have the same shape?
    let result: Bool
    switch (self[a], self[b]) {
    case (let t as Arrow, let u as Arrow):
      result = unifiable(t, u, extending: &subs, handlingCoercionsWith: areCoercible)
    case (_ as AssociatedType, _ as AssociatedType):
      result = false
    case (_ as BuiltinType, _ as BuiltinType):
      result = false
    case (let t as EqualityWitness, let u as EqualityWitness):
      result = unifiable(t, u, extending: &subs, handlingCoercionsWith: areCoercible)
    case (_ as ErrorType, _ as ErrorType):
      result = false
    case (let t as EqualityWitness, let u as EqualityWitness):
      result = unifiable(t, u, extending: &subs, handlingCoercionsWith: areCoercible)
    case (_ as GenericParameter, _ as GenericParameter):
      result = false
    case (let t as Implication, let u as Implication):
      result = unifiable(t, u, extending: &subs, handlingCoercionsWith: areCoercible)
    case (let t as Metatype, let u as Metatype):
      result = unifiable(t, u, extending: &subs, handlingCoercionsWith: areCoercible)
    case (let t as RemoteType, let u as RemoteType):
      result = unifiable(t, u, extending: &subs, handlingCoercionsWith: areCoercible)
    case (_ as Struct, _ as Struct):
      result = false
    case (_ as Trait, _ as Trait):
      result = false
    case (let t as Tuple, let u as Tuple):
      result = unifiable(t, u, extending: &subs, handlingCoercionsWith: areCoercible)
    case (let t as TypeApplication, let u as TypeApplication):
      result = unifiable(t, u, extending: &subs, handlingCoercionsWith: areCoercible)
    case (let t as Union, let u as Union):
      result = unifiable(t, u, extending: &subs, handlingCoercionsWith: areCoercible)
    case (let t as UniversalType, let u as UniversalType):
      result = unifiable(t, u, extending: &subs, handlingCoercionsWith: areCoercible)
    default:
      assert(tag(of: a) != tag(of: b))
      result = false
    }

    return result || areCoercible(a, b)
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: Arrow, _ rhs: Arrow, extending subs: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    (lhs.effect == rhs.effect) && (lhs.isByName == rhs.isByName)
      && lhs.labels.elementsEqual(rhs.labels)
      && unifiable(
        lhs.environment, rhs.environment, extending: &subs, handlingCoercionsWith: areCoercible)
      && unifiable(
        lhs.inputs, rhs.inputs, extending: &subs,
        by: { (a, b, s) in unifiable(a, b, extending: &s, handlingCoercionsWith: areCoercible) })
      && unifiable(
        lhs.output, rhs.output, extending: &subs, handlingCoercionsWith: areCoercible)
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: EqualityWitness, _ rhs: EqualityWitness, extending subs: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    unifiable(lhs.lhs, rhs.lhs, extending: &subs, handlingCoercionsWith: areCoercible)
      && unifiable(lhs.rhs, rhs.rhs, extending: &subs, handlingCoercionsWith: areCoercible)
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: Implication, _ rhs: Implication, extending subs: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    unifiable(lhs.usings, rhs.usings, extending: &subs, handlingCoercionsWith: areCoercible)
      && unifiable(lhs.body, rhs.body, extending: &subs, handlingCoercionsWith: areCoercible)
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: Metatype, _ rhs: Metatype, extending subs: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    unifiable(
      lhs.inhabitant, rhs.inhabitant, extending: &subs, handlingCoercionsWith: areCoercible)
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: RemoteType, _ rhs: RemoteType, extending subs: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    (lhs.access == rhs.access)
      && unifiable(
        lhs.projectee, rhs.projectee, extending: &subs, handlingCoercionsWith: areCoercible)
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: Tuple, _ rhs: Tuple, extending subs: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    unifiable(lhs.elements, rhs.elements, extending: &subs) { (a, b, s) in
      unifiable(a, b, extending: &s, handlingCoercionsWith: areCoercible)
    }
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: Parameter, _ rhs: Parameter, extending subs: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    (lhs.label == rhs.label)
      && unifiable(lhs.type, rhs.type, extending: &subs, handlingCoercionsWith: areCoercible)
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: TypeApplication, _ rhs: TypeApplication, extending subs: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    unifiable(
      lhs.abstraction, rhs.abstraction, extending: &subs, handlingCoercionsWith: areCoercible)
      && unifiable(
        lhs.arguments.values, rhs.arguments.values, extending: &subs,
        by: { (a, b, s) in unifiable(a, b, extending: &s, handlingCoercionsWith: areCoercible) })
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: Union, _ rhs: Union, extending subs: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    unifiable(lhs.elements, rhs.elements, extending: &subs, handlingCoercionsWith: areCoercible)
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: UniversalType, _ rhs: UniversalType, extending subs: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    lhs.parameters.elementsEqual(rhs.parameters)
      && unifiable(lhs.body, rhs.body, extending: &subs, handlingCoercionsWith: areCoercible)
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable(
    _ lhs: Tuple.Element, _ rhs: Tuple.Element, extending subs: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    (lhs.label == rhs.label)
      && unifiable(lhs.type, rhs.type, extending: &subs, handlingCoercionsWith: areCoercible)
  }

  /// Returns `true` if the the pairwise elements of `lhs` and `rhs` are unifiable.
  private func unifiable<T: Sequence<AnyTypeIdentity>>(
    _ lhs: T, _ rhs: T, extending subs: inout SubstitutionTable,
    handlingCoercionsWith areCoercible: CoercionHandler
  ) -> Bool {
    unifiable(lhs, rhs, extending: &subs) { (a, b, s) in
      unifiable(a, b, extending: &s, handlingCoercionsWith: areCoercible)
    }
  }

  /// Returns `true` if `lhs` and `rhs` are unifiable.
  private func unifiable<T: Sequence>(
    _ lhs: T, _ rhs: T, extending subs: inout SubstitutionTable,
    by unify: (T.Element, T.Element, inout SubstitutionTable) -> Bool
  ) -> Bool {
    var i = lhs.makeIterator()
    var j = rhs.makeIterator()
    while let a = i.next() {
      guard let b = j.next(), unify(a, b, &subs) else { return false }
    }
    return j.next() == nil
  }

}

/// The result of a call to a closure passed to `TypeStore.transform(_:)`.
public enum TypeTransformAction {

  case stepInto(AnyTypeIdentity)

  case stepOver(AnyTypeIdentity)

}

/// A closure returning `true` if its first argument can be coerced to the second.
public typealias CoercionHandler = (
  _ lhs: AnyTypeIdentity,
  _ rhs: AnyTypeIdentity
) -> Bool
