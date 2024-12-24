/// A substitution table mapping type and term variables to their values.
internal struct SubstitutionTable {

  /// A policy for substituting variables during reification.
  internal enum SubstitutionPolicy {

    /// Free variables are substituted by errors.
    case substitutedByError

    /// Free variables are kept.
    case kept

  }

  /// A map from type variable to its assignment.
  private var types: [TypeVariable.ID: AnyTypeIdentity]

  /// Creates an empty table.
  internal  init() {
    self.types = [:]
  }

  /// Returns the substitution for `v`, if any.
  internal subscript(v: TypeVariable.ID) -> AnyTypeIdentity? {
    types[walk(v)]
  }

  /// Returns the substitution of `t` in this map or `t` is no such substitution exists.
  internal subscript(t: AnyTypeIdentity) -> AnyTypeIdentity {
    var a = t
    while a.isVariable, let b = types[.init(uncheckedFrom: a)] {
      a = b
    }
    return a
  }

  /// Assigns `substitution` to `variable`.
  mutating func assign(_ substitution: AnyTypeIdentity, to variable: TypeVariable.ID) {
    var walked = variable
    while let a = types[walked] {
      assert(a.isVariable || a == substitution, "variable is already bound")
      walked = .init(uncheckedFrom: a)
    }
    types[walked] = substitution
  }

  /// Returns a copy of `t`, where each variable is substituted by either its corresponding value
  /// in `self` or the application of `substitutionPolicy` is no such substitution exists.
  ///
  /// The default substitution policy is `substituteByError` because we typically use `reify` on
  /// fully formed solutions, thus not expecting any open variables.
  internal func reify(
    _ t: AnyTypeIdentity,
    withVariables substitutionPolicy: SubstitutionPolicy = .substitutedByError
  ) -> AnyTypeIdentity {
    let u = self[t]
    if !u.isVariable || (substitutionPolicy == .kept) {
      return u
    } else {
      return .error
    }
  }

  /// Returns a copy of `self` with its internal representation optimized.
  ///
  /// The optimization consists of minimizing the number of indirections involved in getting the
  /// substitution of a type or term variable. For instance, if `self` contains `%0` -> `%1` and
  /// `%1 -> V`, then `self.optimized()` maps the two variables to `V` directly.
  internal func optimized() -> Self {
    self
  }

  /// Returns the type variable representing the equivalence class of `v` in `self`.
  private func walk(_ v: TypeVariable.ID) -> TypeVariable.ID {
    var w = v
    while let a = types[w], a.isVariable { w = .init(uncheckedFrom: a) }
    return w
  }

}
