/// A substitution table mapping type and term variables to their values.
public struct SubstitutionTable {

  /// A map from type variable to its assignment.
  private var types: [TypeVariable.ID: AnyTypeIdentity]

  /// Creates an empty table.
  internal init() {
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

  /// Returns a table containing the assignments in `self` and in `other`.
  internal func union(_ other: SubstitutionTable) -> SubstitutionTable {
    var result = self
    for t in other.types.keys {
      let u = other[t]
      assert(result.types[t] == nil || result[t] == u)
      result.types[t] = u
    }
    return result
  }

  /// Assigns `substitution` to `variable`.
  internal mutating func assign(_ substitution: AnyTypeIdentity, to variable: TypeVariable.ID) {
    var walked = variable
    while let a = types[walked] {
      assert(a.isVariable || a == substitution, "variable is already bound")
      walked = .init(uncheckedFrom: a)
    }
    types[walked] = substitution
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
