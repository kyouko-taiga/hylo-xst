import Utilities

/// The constraint solving algorithm of Hylo's type system.
internal struct Solver {

  /// A typer for querying type relations and resolve names.
  private var typer: Typer! = nil

  /// The score of the best known solution so far.
  private var best: SolutionScore = .worst

  /// The score of the partial solution computed so far.
  private var current: SolutionScore = .zero

  /// The constraints to satisfy.
  private var goals: [any Constraint] = []

  /// A map from goal its outcome.
  private var outcomes: [GoalOutcome] = []

  /// The set of fresh goals.
  private var fresh: [GoalIdentity] = []

  /// The set of goals that can't be solved yet due to missing type assumptions.
  private var stale: [GoalIdentity] = []

  /// The number of root goals.
  private let rootCount: Int

  /// The type and term substitutions made by the solver.
  ///
  /// This map is monotonically extended during constraint solving to assign a type or term to each
  /// open variable in the constraint system. A system is complete if it can be used to derive a
  /// complete substitution map w.r.t. its open variables.
  private var substitutions = SubstitutionTable()

  /// The name binding assumptions made by the solver.
  ///
  /// This map is monotonically extended during constraint solving to assign a declaration to each
  /// unresolved name expression in the constraint system. A system is complete if it can be used
  /// to derive a complete name binding map w.r.t. its unresolved name expressions.
  private var bindings: BindingTable

  /// A table from call expression to its arguments after elaboration.
  private var elaborations: [(Call.ID, [ParameterBinding])] = []

  /// The current identation level for logging message, or `-1` if logging is disabled.
  private var indentation: Int

  /// Creates an instance for discharging `obligations`, logging a trace of inference steps iff
  /// `loggingIsEnabled` is `true`.
  internal init(_ obligations: Obligations, withLoggingEnabled loggingIsEnabled: Bool) {
    self.bindings = obligations.bindings
    self.rootCount = obligations.constraints.count
    self.indentation = loggingIsEnabled ? 0 : -1
    insert(fresh: obligations.constraints)
  }

  /// Returns a solution discharging the goals in `self` using `typer` for querying type relations
  /// and resolve names.
  internal mutating func solution(using typer: inout Typer) -> Solution {
    solution(betterThanOrEqualTo: .worst, using: &typer)!
  }

  /// Returns a solution discharging the goals in `self` with a score better than or equal to
  /// `best` using `typer` for querying type relations and resolve names.
  internal mutating func solution(
    betterThanOrEqualTo best: SolutionScore, using typer: inout Typer
  ) -> Solution? {
    self.typer = consume typer
    defer { typer = self.typer.sink() }

    log("steps:")
    while let g = fresh.popLast() {
      if current > best {
        log("- abort")
        return nil
      } else {
        goals[g].update({ (t) in substitutions.reify(t, withVariables: .kept) })
        log("- solve: " + self.typer.program.show(goals[g]))
        indenting { (me) in
          assert(me.outcomes[g].isPending, "goal already discharged")
          let o = me.solve(g)
          me.log(outcome: o)
          me.outcomes[g] = o
          if g < me.rootCount && me.outcomes.failed(g) { me.current.errors += 1 }
        }
      }
    }

    assert(goals.indices.allSatisfy({ (g) in !outcomes[g].isPending }))
    return formSolution()
  }

  /// Discharges `g` and stores assumptions about its open variables in `self`.
  private mutating func solve(_ g: GoalIdentity) -> GoalOutcome {
    switch goals[g] {
    case is TypeEquality:
      return solve(equality: g)
    case is CallConstraint:
      return solve(call: g)
    case is ArgumentConstraint:
      return solve(argument: g)
    case is Summonable:
      return solve(summonable: g)
    default:
      unreachable()
    }
  }

  /// Discharges `g`, which is a type equality constraint.
  private mutating func solve(equality g: GoalIdentity) -> GoalOutcome {
    let k = goals[g] as! TypeEquality
    if matches(k.lhs, k.rhs) {
      return .success
    } else {
      return .failure { (s, o, p, d) in
        let t = s.reify(k.lhs)
        let u = s.reify(k.rhs)
        let m = p.format("type '%T' is not compatible with '%T'", [t, u])
        d.insert(.init(.error, m, at: k.site))
      }
    }
  }

  /// Discharges `g`, which is a call constraint.
  private mutating func solve(call g: GoalIdentity) -> GoalOutcome {
    let k = goals[g] as! CallConstraint

    // Can't do anything before we've inferred the type of the callee.
    if k.callee.isVariable {
      return postpone(g)
    }

    switch typer.program[k.origin].style {
    case .parenthesized where !typer.program.types.isArrowLike(k.callee):
      return invalidCallee(k)
    case .bracketed where !typer.program.types.isSubscriptLike(k.callee):
      return invalidCallee(k)
    default:
      break
    }

    let f = typer.program.types[k.callee] as! any Callable
    guard let (bs, cs) = matches(k, inputsOf: f) else {
      return .failure { (_, _, p, d) in
        d.insert(p.incompatibleLabels(found: k.labels, expected: f.labels, at: k.site))
      }
    }
    elaborations.append((k.origin, bs))

    var subgoals = cs.map({ (c) in schedule(c) })
    let m = typer.program.isMarkedMutating(typer.program[k.origin].callee)
    let o = f.output(calleeIsMutating: m)
    subgoals.append(schedule(TypeEquality(lhs: o, rhs: k.output, site: k.site)))

    return delegate(subgoals)
  }

  /// Returns a failure to solve a `k` due to an invalid callee type.
  private func invalidCallee(_ k: CallConstraint) -> GoalOutcome {
    .failure { (s, o, p, d) in
      d.insert(p.cannotCall(s.reify(k.callee), p[k.origin].style, at: p[k.origin].site))
    }
  }

  /// Returns `true` iff `t` and `u` are unifiable.
  private mutating func matches(_ t: AnyTypeIdentity, _ u: AnyTypeIdentity) -> Bool {
    // Is it a trivial cases?
    if t == u {
      return true
    } else if t.isVariable {
      assume(.init(uncheckedFrom: t), equals: u)
      return true
    } else if u.isVariable {
      assume(.init(uncheckedFrom: u), equals: t)
      return true
    }

    // Contains aliases?
    if t[.hasAliases] || u[.hasAliases] {
      return matches(typer.dealiased(t), typer.dealiased(u))
    }

    // Otherwise, compare types side by side.
    switch (typer.program.types[t], typer.program.types[u]) {
    default:
      return false
    }
  }

  /// Returns how the types of the arguments in `k` match the parameters of `f`.
  private mutating func matches(
    _ k: CallConstraint, inputsOf f: any Callable
  ) -> ([ParameterBinding], [ArgumentConstraint])? {
    var bs: [ParameterBinding] = []
    var cs: [ArgumentConstraint] = []

    var i = 0
    for p in f.inputs {
      // Is there's an explicit argument with the right label?
      if (k.arguments.count > i) && (k.arguments[i].label == p.label) {
        let s = typer.program[typer.program[k.origin].arguments[i].value].site
        let a = k.arguments[i]
        bs.append(.explicit(i))
        cs.append(ArgumentConstraint(lhs: a.type, rhs: p.type, site: s))
        i += 1
      }

      // else if f.inputs[i].isImplicit { ... }
      // else if f.inputs[i].hasDefault { ... }

      // Arguments do not match.
      else { return nil }
    }

    assert(bs.count == f.inputs.count)
    return i == k.arguments.count ? (bs, cs) : nil
  }

  /// Extends the term substution table to map `tau` to `substitute`.
  private mutating func assume(_ t: TypeVariable.ID, equals u: AnyTypeIdentity) {
    log("- assume: " + typer.program.format("%T = %T", [t.erased, u]))
    substitutions.assign(u, to: t)
//    refresh()
  }

  /// Discharges `g`, which is an argument constraint.
  private mutating func solve(argument g: GoalIdentity) -> GoalOutcome {
    let k = goals[g] as! ArgumentConstraint

    switch typer.program.types[k.rhs] {
    case is TypeVariable:
      return postpone(g)

    case let p as RemoteType:
      let s = schedule(TypeEquality(lhs: k.lhs, rhs: p.projectee, site: k.site))
      return .split([s]) { (s, _, p, d) in
        let t = s.reify(k.lhs)
        let u = s.reify(k.rhs)
        let m = p.format("cannot pass value of type '%T' to parameter '%T' ", [t, u])
        d.insert(.init(.error, m, at: k.site))
      }

    default:
      return .failure { (s, _, p, d) in
        let t = s.reify(k.rhs)
        let m = p.format("invalid parameter type '%T' ", [t])
        d.insert(.init(.error, m, at: k.site))
      }
    }
  }

  /// Discharges `g`, which is a summonable constraint.
  private mutating func solve(summonable g: GoalIdentity) -> GoalOutcome {
    let k = goals[g] as! Summonable

    // Can't summon until we've inferred free variables.
    if k.type[.hasVariable] {
      return postpone(g)
    }

    let cs = typer.summon(k.type, in: k.scope)
    switch cs.count {
    case 1:
      return .success

    case 0:
      return .failure { (s, o, p, d) in
        let t = s.reify(k.type)
        let m = p.format("no given instance of '%T' in this scope", [t])
        d.insert(.init(.error, m, at: k.site))
      }

    default:
      return .failure { (s, o, p, d) in
        let t = s.reify(k.type)
        let m = p.format("ambiguous given instance of '%T'", [t])
        d.insert(.init(.error, m, at: k.site))
      }
    }
  }

  /// Creates a solution with the current state.
  private mutating func formSolution() -> Solution {
    let ss = substitutions.optimized()
    var ds = DiagnosticSet()

    for g in 0 ..< rootCount {
      if let f = outcomes.diagnosticBuilder(g) {
        f(ss, outcomes, &typer.program, &ds)
      }
    }

    return Solution(substitutions: ss, bindings: bindings, diagnostics: ds)
  }

  /// Inserts `gs` into the fresh set and return their identities.
  @discardableResult
  private mutating func insert<S: Sequence<any Constraint>>(fresh gs: S) -> [GoalIdentity] {
    gs.map({ (g) in insert(fresh: g) })
  }

  /// Inserts `g` into the fresh set and returns its identity.
  private mutating func insert(fresh g: any Constraint) -> GoalIdentity {
    let i = goals.count
    goals.append(g)
    outcomes.append(.pending)
    fresh.append(i)
    return i
  }

  /// Schedules `g` to be solved in the future and returns its identity.
  private mutating func schedule(_ g: Constraint) -> GoalIdentity {
    log("- schedule: \(typer.program.show(g))")
    return insert(fresh: g)
  }

  /// Reschedules `g` to be solved once the solver has inferred more information about at least one
  /// of the free variables occuring in `g`.
  private mutating func postpone(_ g: GoalIdentity) -> GoalOutcome {
    stale.append(g)
    return .pending
  }

  /// Returns the splitting of a goal into sub-goals `gs`, reporting each of failure individually.
  private func delegate(_ gs: [GoalIdentity]) -> GoalOutcome {
    .split(gs) { (m, o, p, d) in
      for g in gs {
        if let f = o.diagnosticBuilder(g) { f(m, o, &p, &d) }
      }
    }
  }

  /// Returns the result of calling `action` on a projection of `self` where `identation` has been
  /// incremented if logging is enabled.
  private mutating func indenting<T>(_ action: (inout Self) -> T) -> T {
    if indentation < 0 {
      return action(&self)
    } else {
      indentation += 1
      defer { indentation -= 1 }
      return action(&self)
    }
  }

  /// Logs a line of text to the standard output iff logging is enabled.
  private func log(_ line: @autoclosure () -> String) {
    if indentation < 0 { return }
    print(String(repeating: "  ", count: indentation) + line())
  }

  /// Logs `o` to the standard output iff loggig is enabled.
  private func log(outcome o: GoalOutcome) {
    log({
      switch o {
      case .pending: "- defer"
      case .success: "- ok"
      case .failure: "- fail"
      case .split: "- split"
      }
    }())
  }

}

/// A closure reporting the diagnostics of a goal's failure into `d`, using `s` to reify types that
/// are defined in `p`, and reading the outcome of other goals from `o`.
private typealias DiagnoseFailure = (
  _ s: SubstitutionTable,
  _ o: [GoalOutcome],
  _ p: inout Program,
  _ d: inout DiagnosticSet
) -> Void

/// The identity of a goal.
private typealias GoalIdentity = Int

/// The outcome of a goal.
private enum GoalOutcome {

  /// The goal hasn't been processed yet.
  case pending

  /// The goal was discharged.
  case success

  /// The goal was unsatisfiable.
  ///
  /// The payload contains a function producing a diagnostic of the failure.
  case failure(DiagnoseFailure)

  /// The goal was split into sub-goals.
  ///
  /// The payload contains the identity of the sub-goals and a function producing a diagnostic of
  /// the failure in case one of the sub-goals is unsatisfiable.
  case split([GoalIdentity], DiagnoseFailure)

  /// `true` iff `self` is `.pending`
  var isPending: Bool {
    if case .pending = self { true } else { false }
  }

}

extension [GoalOutcome] {

  /// Returns `true` iff `g` has failed.
  fileprivate func failed(_ g: GoalIdentity) -> Bool {
    switch self[g] {
    case .failure:
      return true
    case .split(let gs, _):
      return gs.contains(where: failed(_:))
    default:
      return false
    }
  }

  /// If `g` has failed, returns the function producing its diagnostic.
  fileprivate func diagnosticBuilder(_ g: GoalIdentity) -> DiagnoseFailure? {
    switch self[g] {
    case .pending, .success:
      return nil
    case .failure(let f):
      return f
    case .split(let gs, let f):
      return gs.contains(where: failed(_:)) ? f : nil
    }
  }

}

/// A value measuring the correctness of a solution.
internal struct SolutionScore {

  /// The raw value of the score.
  private var rawValue: UInt64

  /// Creates an instance with the given raw value.
  private init(rawValue: UInt64) {
    self.rawValue = rawValue
  }

  /// Creates an instance with the given properties.
  internal init(errors: Int, penalties: Int) {
    assert(errors < UInt32.max && penalties < UInt32.max)
    self.rawValue = UInt64(errors) << 32 | UInt64(penalties)
  }

  /// The number of unsatisfiable root goals.
  internal var errors: Int {
    get { Int(truncatingIfNeeded: rawValue >> 32) }
    set { self.rawValue = UInt64(newValue) << 32 | UInt64(penalties) }
  }

  /// The number of penalties associated with the solution.
  internal var penalties: Int {
    get { Int(truncatingIfNeeded: rawValue & ((1 << 32) - 1)) }
    set { self.rawValue = UInt64(errors) << 32 | UInt64(newValue) }
  }

  /// The best possible score.
  internal static var zero: SolutionScore { .init(rawValue: 0) }

  /// The worst possible score.
  internal static var worst: SolutionScore { .init(rawValue: .max) }

}

extension SolutionScore: Comparable {

  internal static func < (l: Self, r: Self) -> Bool {
    l.rawValue < r.rawValue
  }

}
