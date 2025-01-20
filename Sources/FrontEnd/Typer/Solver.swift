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
  private var elaborations: [(Call.ID, ParameterBindings)] = []

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

  /// Returns a copy of `base` with its `typer` set to `nil`.
  private init (forking base: Self) {
    self = base
    self.typer = nil
  }

  /// Returns a solution discharging the goals in `self` using `typer` for querying type relations
  /// and resolve names.
  internal mutating func solution(using typer: inout Typer) -> Solution {
    log("steps:")
    return solution(betterThanOrEqualTo: .worst, using: &typer)!
  }

  /// Returns a solution discharging the goals in `self` with a score better than or equal to
  /// `best` using `typer` for querying type relations and resolve names.
  private mutating func solution(
    betterThanOrEqualTo best: SolutionScore, using typer: inout Typer
  ) -> Solution? {
    self.typer = consume typer
    defer { typer = self.typer.sink() }

    while let g = fresh.popLast() {
      if current > best {
        log("- abort")
        return nil
      } else {
        goals[g].update { (t) in
          self.typer.program.types.reify(t, applying: substitutions, withVariables: .kept)
        }
        log("- solve: " + self.typer.program.show(goals[g]))

        let s = indenting { (me) -> Solution? in
          assert(me.outcomes[g].isPending, "goal already discharged")

          let o: GoalOutcome
          switch me.goals[g] {
          case is EqualityConstraint:
            o = me.solve(equality: g)
          case is CoercionConstraint:
            o = me.solve(coercion: g)
          case is WideningConstraint:
            o = me.solve(widening: g)
          case is CallConstraint:
            o = me.solve(call: g)
          case is ArgumentConstraint:
            o = me.solve(argument: g)
          case is StaticCallConstraint:
            o = me.solve(staticCall: g)
          case is Summonable:
            o = me.solve(summonable: g)
          case is OverloadConstraint:
            return me.solve(overload: g)
          default:
            unreachable()
          }

          me.log(outcome: o)
          me.outcomes[g] = o
          if me.outcomes.failed(g) { me.current.errors += 1 }
          return nil
        }

        if let result = s { return result }
      }

      if fresh.isEmpty { refreshCoercionAndWideningConstraints() }
    }

    // Not enough context to solve the remaining stale constraints.
    while let g = stale.popLast() {
      outcomes[g] = .failure { (_, _, _, _) in
        ()  // TODO: Diagnose stale constraints
      }
    }

    assert(goals.indices.allSatisfy({ (g) in !outcomes[g].isPending }))
    return formSolution()
  }

  /// Discharges `g`, which is an equality constraint.
  private mutating func solve(equality g: GoalIdentity) -> GoalOutcome {
    let k = goals[g] as! EqualityConstraint

    if let s = typer.program.types.unifiable(k.lhs, k.rhs) {
      for (t, u) in s.types.sorted(by: \.key.erased.bits) { assume(t, equals: u) }
      return .success
    } else {
      return .failure { (s, _, p, d) in
        let t = p.types.reify(k.lhs, applying: s)
        let u = p.types.reify(k.rhs, applying: s)
        let m = p.format("type '%T' is not compatible with '%T'", [t, u])
        d.insert(.init(.error, m, at: k.site))
      }
    }
  }

  /// Discharges `g`, which is a coercion constraint.
  private mutating func solve(coercion g: GoalIdentity) -> GoalOutcome {
    let k = goals[g] as! CoercionConstraint

    if k.isTrivial {
      return .success
    } else if k.lhs.isVariable || k.rhs.isVariable {
      return postpone(g)
    }

    let e = typer.program.types.demand(EqualityWitness(lhs: k.lhs, rhs: k.rhs)).erased
    if let w = typer.summon(e, in: typer.program.parent(containing: k.origin)).uniqueElement {
      _ = w // TODO: Store elaboration
      return .success
    } else if k.lhs[.hasVariable] || k.rhs[.hasVariable] {
      return postpone(g)
    } else {
      return .failure { (s, _, p, d) in
        let t = p.types.reify(k.lhs, applying: s)
        let u = p.types.reify(k.rhs, applying: s)
        d.insert(p.noCoercion(from: t, to: u, at: k.site))
      }
    }
  }

  /// Discharges `g`, which is a widening constraint.
  private mutating func solve(widening g: GoalIdentity) -> GoalOutcome {
    let k = goals[g] as! WideningConstraint

    // Otherwise, check that the left-hand side can be widened to the right-hand side.
    switch typer.program.types[k.rhs] {
    case is TypeVariable:
      return postpone(g)

    case let u as Union:
      if u.elements.isEmpty {
        return .success
      } else if k.lhs.isVariable || u.elements.contains(where: \.isVariable) {
        return postpone(g)
      } else {
        fatalError("TODO")
      }

    default:
      return simplify(k)
    }
  }

  /// Returns the simplification of `k` as an equality between its operands.
  private mutating func simplify(_ k: CoercionConstraint) -> GoalOutcome {
    let e = EqualityConstraint(lhs: k.lhs, rhs: k.rhs, site: k.site)
    let s = schedule(e)
    return .forward([s]) { (s, _, p, d) in
      let t = p.types.reify(e.lhs, applying: s)
      let u = p.types.reify(e.rhs, applying: s)
      d.insert(p.noCoercion(from: t, to: u, at: e.site))
    }
  }

  /// Returns the simplification of `k` as an equality between its operands.
  private mutating func simplify(_ k: WideningConstraint) -> GoalOutcome {
    let e = EqualityConstraint(lhs: k.lhs, rhs: k.rhs, site: k.site)
    let s = schedule(e)
    return .forward([s]) { (s, _, p, d) in
      let t = p.types.reify(e.lhs, applying: s)
      let u = p.types.reify(e.rhs, applying: s)
      d.insert(p.noConversion(from: t, to: u, at: e.site))
    }
  }

  /// Discharges `g`, which is a call constraint.
  private mutating func solve(call g: GoalIdentity) -> GoalOutcome {
    let k = goals[g] as! CallConstraint

    // Can't do anything before we've inferred the type of the callee.
    let callee = typer.program.types.head(k.callee)
    if callee.isVariable {
      return postpone(g)
    }

    // Check that the callee has the right shape.
    switch typer.program[k.origin].style {
    case .parenthesized where !typer.program.types.isArrowLike(callee):
      return invalidCallee(k)
    case .bracketed where !typer.program.types.isSubscriptLike(callee):
      return invalidCallee(k)
    default:
      break
    }

    // Insert compile-time implicits.
    let scopeOfUse = typer.program.parent(containing: k.origin)
    let calleeSite = typer.program[typer.program[k.origin].callee].site
    var subgoals: [any Constraint] = []
    let adaptedCallee = adaptCalleeType(
      k.callee, in: scopeOfUse, at: calleeSite, addingSubgoalsInto: &subgoals)

    // Check that the argument list has the right shape.
    guard let bs = matches(k, inputsOf: adaptedCallee, addingSubgoalsInto: &subgoals) else {
      return .failure { (_, _, p, d) in
        d.insert(p.incompatibleLabels(found: k.labels, expected: adaptedCallee.labels, at: k.site))
      }
    }
    if bs.hasDefaulted {
      elaborations.append((k.origin, bs))
    }

    // Constrain the return type.
    let m = typer.program.isMarkedMutating(typer.program[k.origin].callee)
    let o = adaptedCallee.output(calleeIsMutating: m)
    subgoals.append(EqualityConstraint(lhs: o, rhs: k.output, site: k.site))

    // Simplify the constraint.
    let cs = subgoals.map({ (s) in schedule(s) })
    return delegate(cs)
  }

  /// Adds constraints to resolve the arguments to the compile-time context parameters of a callee
  /// of type `t` in `scopeOfUse` at `site` at the end of `subgoals`.
  private mutating func adaptCalleeType(
    _ t: AnyTypeIdentity, in scopeOfUse: ScopeIdentity, at site: SourceSpan,
    addingSubgoalsInto subgoals: inout [any Constraint]
  ) -> any Callable {
    switch typer.program.types[t] {
    case let u as UniversalType:
      let subs = Dictionary(
        uniqueKeysWithValues: u.parameters.map({ (p) in
          (p.erased, typer.program.types.fresh().erased)
        }))
      let open = typer.program.types.substitute(subs, in: u.body)
      return adaptCalleeType(open, in: scopeOfUse, at: site, addingSubgoalsInto: &subgoals)

    case let u as Implication:
      for t in u.context {
        subgoals.append(Summonable(type: t, scope: scopeOfUse, site: site))
      }
      return adaptCalleeType(u.head, in: scopeOfUse, at: site, addingSubgoalsInto: &subgoals)

    case let u:
      return u as! any Callable
    }
  }

  /// Returns how the types of the arguments in `k` match the parameters of `f`.
  private mutating func matches(
    _ k: CallConstraint, inputsOf f: any Callable,
    addingSubgoalsInto subgoals: inout [any Constraint]
  ) -> ParameterBindings? {
    var bindings = ParameterBindings()

    var i = 0
    for p in f.inputs {
      // Is there's an explicit argument with the right label?
      if (k.arguments.count > i) && (k.arguments[i].label == p.label) {
        let v = typer.program[k.origin].arguments[i].value
        let a = k.arguments[i]
        bindings.append(.explicit(i))
        subgoals.append(
          ArgumentConstraint(origin: v, lhs: a.type, rhs: p.type, site: typer.program[v].site))
        i += 1
      }

      // The parameter has a default value?
      else if let d = p.declaration, typer.program[d].default != nil {
        bindings.append(.defaulted(d))
        continue
      }

      // TODO: Run-time implicits

      // Arguments do not match.
      else { return nil }
    }

    assert(bindings.elements.count == f.inputs.count)
    return i == k.arguments.count ? bindings : nil
  }

  /// Returns a failure to solve a `k` due to an invalid callee type.
  private func invalidCallee(_ k: CallConstraint) -> GoalOutcome {
    .failure { (s, o, p, d) in
      let t = p.types.reify(k.callee, applying: s)
      d.insert(p.cannotCall(t, p[k.origin].style, at: p[k.origin].site))
    }
  }

  /// Discharges `g`, which is an argument constraint.
  private mutating func solve(argument g: GoalIdentity) -> GoalOutcome {
    let k = goals[g] as! ArgumentConstraint

    switch typer.program.types[k.rhs] {
    case is TypeVariable:
      return postpone(g)

    case let p as RemoteType:
      let s = schedule(
        CoercionConstraint(
          on: k.origin, from: k.lhs, to: p.projectee, reason: .unspecified, at: k.site))
      return .forward([s]) { (s, _, p, d) in
        let t = p.types.reify(k.lhs, applying: s)
        let u = p.types.reify(k.rhs, applying: s)
        let m = p.format("cannot pass value of type '%T' to parameter '%T'", [t, u])
        d.insert(.init(.error, m, at: k.site))
      }

    default:
      return .failure { (s, _, p, d) in
        let t = p.types.reify(k.rhs, applying: s)
        let m = p.format("invalid parameter type '%T' ", [t])
        d.insert(.init(.error, m, at: k.site))
      }
    }
  }

  /// Discharges `g`, which is a static call constraint.
  private mutating func solve(staticCall g: GoalIdentity) -> GoalOutcome {
    let k = goals[g] as! StaticCallConstraint

    // Can't do anything before we've inferred the type of the callee.
    if k.callee.isVariable {
      return postpone(g)
    }

    // Is the callee applicable?
    guard let f = typer.program.types[k.callee] as? UniversalType else {
      return invalidArgumentCount(k, expected: 0)
    }
    if f.parameters.count != k.arguments.count {
      return invalidArgumentCount(k, expected: f.parameters.count)
    }

    var ss: [AnyTypeIdentity: AnyTypeIdentity] = .init(minimumCapacity: f.parameters.count)
    for (p, a) in zip(f.parameters, k.arguments) {
      ss[p.erased] = (typer.program.types[a] as? Metatype)?.inhabitant ?? .error
    }

    let body = typer.program.types.substitute(ss, in: f.body)
    let subgoal = schedule(EqualityConstraint(lhs: k.output, rhs: body, site: k.site))
    return delegate([subgoal])
  }

  /// Returns a failure to solve a `k` due to an invalid number of arguments.
  private func invalidArgumentCount(
    _ k: StaticCallConstraint, expected: Int
  ) -> GoalOutcome {
    .failure { (s, _, p, d) in
      let f = if let n = p.cast(p[k.origin].callee, to: NameExpression.self) {
        "'\(p[n].name)'"
      } else {
        p.format("value of type '%T'", [p.types.reify(k.callee, applying: s)])
      }

      let m = if expected == 0 {
        "\(f) takes no compile-time arguments"
      } else {
        "\(f) takes \(expected) compile-time argument(s); found \(k.arguments.count)"
      }

      d.insert(.init(.error, m, at: p.spanForDiagnostic(about: p[k.origin].callee)))
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
        let t = p.types.reify(k.type, applying: s)
        let m = p.format("no given instance of '%T' in this scope", [t])
        d.insert(.init(.error, m, at: k.site))
      }

    default:
      return .failure { (s, o, p, d) in
        let t = p.types.reify(k.type, applying: s)
        let m = p.format("ambiguous given instance of '%T'", [t])
        d.insert(.init(.error, m, at: k.site))
      }
    }
  }

  /// Discharges `g`, which is an overload constraint.
  private mutating func solve(overload g: GoalIdentity) -> Solution {
    let k = goals[g] as! OverloadConstraint

    var viable: [(choice: NameResolutionCandidate, solution: Solution)] = []
    for choice in k.candidates {
      let equality = EqualityConstraint(lhs: k.type, rhs: choice.type, site: k.site)
      log("- pick: \(typer.program.show(equality))")

      let s = indenting { (me) in
        var fork = Self(forking: me)
        let s = fork.insert(fresh: equality)
        fork.outcomes[g] = fork.delegate([s])
        fork.bindings[k.name] = choice.reference
        return fork.solution(betterThanOrEqualTo: me.best, using: &me.typer)
      }

      if let newSolution = s {
        let newScore = SolutionScore(
          errors: newSolution.diagnostics.elements.count, penalties: current.penalties)

        if newScore < best {
          best = newScore
          viable = [(choice, newSolution)]
        } else {
          viable.append((choice, newSolution))
        }
      }
    }

    let scopeOfUse = typer.program.parent(containing: k.name)
    let least = viable.least { (a, b) in
      typer.program.isPreferred(a.choice, other: b.choice, in: scopeOfUse)
    }

    if let (_, s) = least {
      return s
    } else {
      // There must be at least one solution.
      var s = viable[0].solution
      let d = Diagnostic(
        .error, "ambiguous use of '\(typer.program[k.name].name.value)'", at: k.site)
      s.add(d)
      return s
    }
  }

  /// Creates a solution with the current state.
  private mutating func formSolution() -> Solution? {
    if current > best { return nil }

    let ss = substitutions.optimized()
    var ds = DiagnosticSet()

    for g in 0 ..< rootCount {
      if let f = outcomes.diagnosticBuilder(g) {
        f(ss, outcomes, &typer.program, &ds)
      }
    }

    return Solution(
      substitutions: ss, bindings: bindings, elaborations: elaborations,
      diagnostics: ds)
  }

  /// Assumes that `n` refers to `r`.
  private mutating func assume(_ n: NameExpression.ID, boundTo r: DeclarationReference) {
    bindings[n] = r
  }

  /// Assumes that `t` is assigned to `u`.
  private mutating func assume(_ t: TypeVariable.ID, equals u: AnyTypeIdentity) {
    log("- assume: " + typer.program.format("%T = %T", [t.erased, u]))
    substitutions.assign(u, to: t)
    refresh()
  }

  /// Refresh constraints containing type variables that have been assigned.
  private mutating func refresh() {
    // Nothing to do if the stale set is empty.
    if stale.isEmpty { return }

    var end = stale.count
    for i in (0 ..< stale.count).reversed() {
      var changed = false
      goals[stale[i]].update { (t) in
        let u = typer.program.types.reify(t, applying: substitutions, withVariables: .kept)
        if t != u { changed = true }
        return u
      }

      if changed {
        log("- refresh: " + typer.program.show(goals[stale[i]]))
        fresh.append(stale[i])
        stale.swapAt(i, end - 1)
        end -= 1
      }
    }
    stale.removeSubrange(end...)
  }

  /// Transforms all stale coercion and widening constraints into equality constraints, selecting
  /// upper/lower bounds using to the current type assignments.
  private mutating func refreshCoercionAndWideningConstraints() {
    // Nothing to do if the stale set is empty.
    if stale.isEmpty { return }

    var end = stale.count
    for i in (0 ..< stale.count).reversed() {
      switch goals[stale[i]] {
      case let k as CoercionConstraint:
        outcomes[stale[i]] = simplify(k)
      case let k as WideningConstraint:
        outcomes[stale[i]] = simplify(k)
      default:
        continue
      }
      stale.swapAt(i, end - 1)
      end -= 1
    }

    stale.removeSubrange(end...)
  }

  /// Inserts `gs` into the fresh set and return their identities.
  @discardableResult
  private mutating func insert<S: Sequence<any Constraint>>(fresh gs: S) -> [GoalIdentity] {
    gs.map({ (g) in insert(fresh: g) })
  }

  /// Inserts `k` into the fresh set and returns its identity.
  private mutating func insert(fresh k: any Constraint) -> GoalIdentity {
    let g = goals.count
    goals.append(k)
    if k.isTrivial && false {
      outcomes.append(.success)
    } else {
      outcomes.append(.pending)
      fresh.append(g)
    }
    return g
  }

  /// Schedules `k` to be solved in the future and returns its identity.
  private mutating func schedule(_ k: Constraint) -> GoalIdentity {
    log("- schedule: \(typer.program.show(k))")
    return insert(fresh: k)
  }

  /// Reschedules `g` to be solved once the solver has inferred more information about at least one
  /// of the free variables occuring in `g`.
  private mutating func postpone(_ g: GoalIdentity) -> GoalOutcome {
    stale.append(g)
    return .pending
  }

  /// Returns the splitting of a goal into sub-goals `gs`, reporting each of failure individually.
  private func delegate(_ gs: [GoalIdentity]) -> GoalOutcome {
    .forward(gs) { (m, o, p, d) in
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
      case .forward: "- forward"
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
  case forward([GoalIdentity], DiagnoseFailure)

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
    case .forward(let gs, _):
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
    case .forward(let gs, let f):
      return gs.contains(where: failed(_:)) ? f : nil
    }
  }

}

/// A value measuring the correctness of a solution.
private struct SolutionScore {

  /// The raw value of the score.
  private var rawValue: UInt64

  /// Creates an instance with the given raw value.
  private init(rawValue: UInt64) {
    self.rawValue = rawValue
  }

  /// Creates an instance with the given properties.
  fileprivate init(errors: Int, penalties: Int) {
    assert(errors < UInt32.max && penalties < UInt32.max)
    self.rawValue = UInt64(errors) << 32 | UInt64(penalties)
  }

  /// The number of unsatisfiable root goals.
  fileprivate var errors: Int {
    get { Int(truncatingIfNeeded: rawValue >> 32) }
    set { self.rawValue = UInt64(newValue) << 32 | UInt64(penalties) }
  }

  /// The number of penalties associated with the solution.
  fileprivate var penalties: Int {
    get { Int(truncatingIfNeeded: rawValue & ((1 << 32) - 1)) }
    set { self.rawValue = UInt64(errors) << 32 | UInt64(newValue) }
  }

  /// The best possible score.
  fileprivate static var zero: SolutionScore { .init(rawValue: 0) }

  /// The worst possible score.
  fileprivate static var worst: SolutionScore { .init(rawValue: .max) }

}

extension SolutionScore: Comparable {

  internal static func < (l: Self, r: Self) -> Bool {
    l.rawValue < r.rawValue
  }

}
