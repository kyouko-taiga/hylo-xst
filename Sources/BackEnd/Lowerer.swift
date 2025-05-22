import FrontEnd

/// The lowering algorithm of a Hylo program.
public struct Lowerer {

  /// The module being translated.
  public let module: Program.ModuleIdentity

  /// The program containing the module being translated.
  public internal(set) var program: Program

  /// The translated program.
  public internal(set) var ir: IRProgram

  /// Creates an instance translating `m`, which is a module in `p`.
  public init(translating m: Program.ModuleIdentity, of p: consuming Program) {
    self.module = m
    self.program = p
    self.ir = IRProgram()
  }

  /// Translates the top-level declarations of `self.module`.
  public mutating func apply() {
    for d in program[module].topLevelDeclarations {
      let x = translate(d)
      assert(x == .void)
    }
  }

  /// Returns the resources held by this instance.
  public consuming func release() -> Program {
    self.program
  }

  /// Translates `d`.
  private mutating func translate(_ d: DeclarationIdentity) -> IRTree {
    switch program.tag(of: d) {
    case BindingDeclaration.self:
      return translate(program.castUnchecked(d, to: BindingDeclaration.self))
    case FunctionDeclaration.self:
      return translate(program.castUnchecked(d, to: FunctionDeclaration.self))
    case StructDeclaration.self:
      return translate(program.castUnchecked(d, to: StructDeclaration.self))
    default:
      program.unexpected(d)
    }
  }

  /// Translates `d`.
  private mutating func translate(_ d: BindingDeclaration.ID) -> IRTree {
    let p = program[program[d].pattern].pattern

    // We only support simple binding patterns.
    guard let v = program.cast(p, to: VariableDeclaration.self) else {
      program.unexpected(p)
    }

    let n = ir.identifier(of: v, using: program)
    let t = ir.type(assignedTo: v, using: program)
    var result = [IRTree.variable(identifier: n, type: t)]

    if let i = program[d].initializer {
      let s = translate(i)
      result.append(.copy(target: .identifier(n), source: s, type: t))
    }

    return .init(result)
  }

  /// Translates `d`.
  private mutating func translate(_ d: FunctionDeclaration.ID) -> IRTree {
    // Memberwise initializers are not compiled to functions.
    if program[d].isMemberwiseInitializer { return .void }

    let n = ir.declare(function: d, using: program)
    if let b = program[d].body {
      // Is the function body empty?
      if b.isEmpty {
        ir.define(function: n, body: .void)
      }

      // Is the function defined as a single expression?
      else if let e = b.uniqueElement.flatMap(program.castToExpression(_:)) {
        let t = program.typeSansEffect(assignedTo: e)
        let v = translate(e)
        ir.define(function: n, body: .return(source: v, type: t))
      }

      // Otheriwse, assume there are return statements.
      else {
        let statements: [IRTree] = b.reduce(into: []) { (ss, s) in
          ss.append(translate(s))
        }
        ir.define(function: n, body: .init(statements))
      }
    }

    return .void
  }

  /// Translates `d`.
  private mutating func translate(_ d: StructDeclaration.ID) -> IRTree {
    for m in program[d].members {
      // Nothing to do for stored properties.
      if program.tag(of: m) == BindingDeclaration.self { continue }
      let x = translate(m)
      assert(x == .void)
    }
    return .void
  }

  /// Translates `e`.
  private mutating func translate(_ e: ExpressionIdentity) -> IRTree {
    switch program.tag(of: e) {
    case BooleanLiteral.self:
      return translate(program.castUnchecked(e, to: BooleanLiteral.self))
    case Call.self:
      return translate(program.castUnchecked(e, to: Call.self))
    case If.self:
      return translate(program.castUnchecked(e, to: If.self))
    case InoutExpression.self:
      return translate(program.castUnchecked(e, to: InoutExpression.self))
    case NameExpression.self:
      return translate(program.castUnchecked(e, to: NameExpression.self))
    default:
      program.unexpected(e)
    }
  }

  /// Translates `e`.
  private mutating func translate(_ e: BooleanLiteral.ID) -> IRTree {
    let x = ir.fresh()
    let t = program.typeSansEffect(assignedTo: e)
    let u = program.types.demand(MachineType.i(1))
    let result: [IRTree] = [
      .variable(identifier: x, type: t),
      .store(target: .identifier(x), source: .bool(program[e].value), type: u),
      .identifier(x),
    ]
    return .init(result)
  }

  /// Translates `e`.
  private mutating func translate(_ e: Call.ID) -> IRTree {
    let callee: ExpressionIdentity
    let typeArguments: TypeArguments

    // Extract the expression of the callee and its type arguments if any.
    if let f = program.cast(program[e].callee, to: SynthethicExpression.self) {
      guard case .witness(let w) = program[f].value else { program.unexpected(f) }
      (callee, typeArguments) = calleeAndTypeArguments(w)
    } else {
      callee = program[e].callee
      typeArguments = .init()
    }

    // Are we calling a constructor?
    if let f = constructor(referredToBy: callee) {
      return application(constructor: f, appliedTo: typeArguments, toArgumentsOf: e)
    }

    // Are we calling a built-in function?
    else if let f = builtinFunction(referredToBy: callee) {
      assert(typeArguments.isEmpty)
      return application(builtin: f, toArgumentsOf: e)
    }

    // Are we calling a function referred to by name?
    else if let n = program.cast(sansMutationMarker(callee), to: NameExpression.self) {
      switch program.declaration(referredToBy: n) {
      case .member(let d):
        let q = program[n].qualification!
        return application(member: d, of: q, appliedTo: typeArguments, toArgumentsOf: e)
      default:
        program.unexpected(callee)
      }
    }

    // Other forms of function calls are not supported.
    else { program.unexpected(e) }

    func calleeAndTypeArguments(_ w: WitnessExpression) -> (ExpressionIdentity, TypeArguments) {
      switch w.value {
      case .typeApplication(let f, let a):
        let (e, b) = calleeAndTypeArguments(f)
        assert(b.isEmpty)
        return (e, a)

      case .identity(let e):
        return (e, .init())

      default:
        program.unexpected(program[e].callee)
      }
    }
  }

  /// Returns the translation of an application of `f` to the arguments of `e`.
  private mutating func application(
    builtin f: BuiltinFunction,
    toArgumentsOf e: Call.ID
  ) -> IRTree {
    let arguments: [IRTree] = program[e].arguments.map { (a) in
      let v = translate(a.value)
      let t = program.typeSansEffect(assignedTo: a.value)
      return v.isBuiltinCall ? v : .load(source: v, type: program.types.castUnchecked(t))
    }
    return .builtinCall(f, arguments)
  }

  /// Returns the translation of an application of `f` to the arguments of `e`.
  private mutating func application(
    constructor d: FunctionDeclaration.ID, appliedTo a: TypeArguments,
    toArgumentsOf e: Call.ID
  ) -> IRTree {
    // Allocate storage for the newly constructed instance.
    let t = program.typeSansEffect(assignedTo: e)
    let x = ir.fresh()
    var result = [IRTree.variable(identifier: x, type: t)]

    // Are we translating memberwise initialization?
    if program[d].isMemberwiseInitializer {
      for (i, a) in program[e].arguments.enumerated() {
        let u = program.typeSansEffect(assignedTo: a.value)
        let l = IRTree.field(i, source: .identifier(x), type: t)
        let r = translate(a.value)
        result.append(assignment(to: l, source: r, of: u))
      }
    }

    // Otherwise it's just a regular member call.
    else {
      // The first argument is a pointer to the newly allocated storage.
      var arguments: [IRTree] = [.nullptr, .identifier(x)]
      for a in program[e].arguments {
        let u = program.typeSansEffect(assignedTo: a.value)
        let r = translate(a.value)
        arguments.append(lvalue(r, instanceOf: u))
      }

      let y = IRTree.identifier(ir.identifier(of: d, using: program))
      let z = a.isEmpty ? y : .typeApplication(abstraction: y, arguments: a)
      result.append(.call(z, arguments))
    }

    result.append(.identifier(x))
    return .init(result)
  }

  /// Returns the translation of an application of `f` to the arguments of `e`.
  private mutating func application(
    member d: DeclarationIdentity, of q: ExpressionIdentity, appliedTo a: TypeArguments,
    toArgumentsOf e: Call.ID
  ) -> IRTree {
    // Allocate storage for the newly constructed instance.
    let t = program.typeSansEffect(assignedTo: e)
    let x = ir.fresh()
    var result = [IRTree.variable(identifier: x, type: t)]

    var arguments = [IRTree.identifier(x)]
    arguments.append(translate(q))
    arguments.append(contentsOf: program[e].arguments.map({ (a) in translate(a.value) }))

    let y = IRTree.identifier(ir.identifier(of: d, using: program))
    let z = a.isEmpty ? y : .typeApplication(abstraction: y, arguments: a)
    result.append(.call(z, arguments))
    result.append(.identifier(x))
    return .init(result)
  }

  /// Returns the translation of the code storing the value of `source`, which is an instance of
  /// `type`, to `target`.
  ///
  /// If `type` is a machine type, `source` is assumed to produce a rvalue (i.e., a value that is
  /// not stored in memory) and the translation is a `store` instruction. Otherwise, `source` is
  /// assumed to produce a rvalue (i.e., a value that is stored in memory) and the translation is a
  /// `copy` instruction.
  private mutating func assignment(
    to target: IRTree, source: IRTree, of type: AnyTypeIdentity
  ) -> IRTree {
    if let m = program.types.cast(type, to: MachineType.self) {
      return .store(target: target, source: source, type: m)
    } else {
      return .copy(target: target, source: lvalue(source, instanceOf: type), type: type)
    }
  }

  /// Translates `e`.
  private mutating func translate(_ e: If.ID) -> IRTree {
    guard let condition = program[e].conditions.uniqueElement else {
      program.unexpected(program[e].conditions[1])
    }

    if let c = program.castToExpression(condition) {
      let x0 = translate(c)
      let x1 = translate(program[e].success)
      let x2 = translate(program[e].failure)
      return .if(x0, then: x1, else: x2)
    } else {
      fatalError("unsupported condition at \(program[condition].site)")
    }
  }

  /// Translates `e`.
  private mutating func translate(_ e: If.ElseIdentity) -> IRTree {
    switch program.tag(of: e) {
    case Block.self:
      return translate(program.castUnchecked(e, to: Block.self))
    case If.self:
      return translate(program.castUnchecked(e, to: If.self))
    default:
      program.unexpected(e)
    }
  }

  /// Translates `e`.
  private mutating func translate(_ e: InoutExpression.ID) -> IRTree {
    translate(program[e].lvalue)
  }

  /// Translates `e`.
  private mutating func translate(_ e: NameExpression.ID) -> IRTree {
    switch program.declaration(referredToBy: e) {
    case .some(.direct(let d)):
      return .identifier(ir.identifier(of: d, using: program))

    case .some(.member(let d)):
      let qualification = program[e].qualification!

      if let f = program.cast(d, to: VariableDeclaration.self) {
        let q = translate(qualification)
        let i = ir.fieldIndex(of: f, using: program)
        return .field(i, source: q, type: program.typeSansEffect(assignedTo: qualification))
      } else {
        program.unexpected(e)
      }

    default:
      fatalError("unsupported declaration reference at \(program[e].site)")
    }
  }

  /// Translates `w`.
  private mutating func translate(_ w: WitnessExpression, at site: SourceSpan) -> IRTree {
    switch w.value {
    case .identity(let e):
      return translate(e)
    case .reference(let r):
      return translate(r, at: site)
    case .typeApplication(let f, let a):
      return .typeApplication(abstraction: translate(f, at: site), arguments: a)
    default:
      fatalError("unsupported expression '\(program.show(w))' at \(site)")
    }
  }

  /// Translates `r`.
  private mutating func translate(_ r: DeclarationReference, at site: SourceSpan) -> IRTree {
    switch r {
    case .direct(let d):
      return .identifier(ir.identifier(of: d, using: program))
    default:
      fatalError("unsupported declaration reference at \(site)")
    }
  }

  /// Translates `s`.
  private mutating func translate(_ s: StatementIdentity) -> IRTree {
    switch program.tag(of: s) {
    case Assignment.self:
      return translate(program.castUnchecked(s, to: Assignment.self))
    case Block.self:
      return translate(program.castUnchecked(s, to: Block.self))
    case Discard.self:
      return translate(program.castUnchecked(s, to: Discard.self))

    default:
      if let d = program.castToDeclaration(s) {
        return translate(d)
      } else if let e = program.castToExpression(s) {
        return translate(e)
      } else {
        program.unexpected(s)
      }
    }
  }

  /// Translates `s`.
  private mutating func translate(_ s: Assignment.ID) -> IRTree {
    let t = program.typeSansEffect(assignedTo: program[s].lhs)
    let l = translate(program[s].lhs)
    let r = translate(program[s].rhs)
    return assignment(to: l, source: r, of: t)
  }

  /// Translates `s`.
  private mutating func translate(_ s: Block.ID) -> IRTree {
    let statements: [IRTree] = program[s].statements.reduce(into: []) { (ss, s) in
      ss.append(translate(s))
    }
    return .init(statements)
  }

  /// Translates `s`.
  private mutating func translate(_ s: Discard.ID) -> IRTree {
    let t = program.typeSansEffect(assignedTo: program[s].value)
    return .discard(source: translate(program[s].value), type: t)
  }

  /// Returns `e`, which denotes an expression of type `t`, as a lvalue.
  private mutating func lvalue(_ e: IRTree, instanceOf t: AnyTypeIdentity) -> IRTree {
    switch e {
    case .load(let s, _):
      return s

    case .builtinCall:
      let x = ir.fresh()
      let p: [IRTree] = [
        .variable(identifier: x, type: t),
        .store(target: .identifier(x), source: e, type: program.types.castUnchecked(t)),
      ]
      return .block(prefix: p, last: .identifier(x))

    default:
      return e
    }
  }

  /// If `e` refers to an initializer used as a constructor, returns that function.
  private func constructor(referredToBy e: ExpressionIdentity) -> FunctionDeclaration.ID? {
    if
      let x0 = program.cast(e, to: New.self),
      let x1 = program.declaration(referredToBy: program[x0].target)?.target,
      let x2 = program.cast(x1, to: FunctionDeclaration.self)
    {
      return x2
    } else {
      return nil
    }
  }

  /// If `e` refers to a built-in function, returns that function.
  private func builtinFunction(referredToBy e: ExpressionIdentity) -> BuiltinFunction? {
    program.cast(e, to: NameExpression.self).flatMap { (n) in
      if case .builtin(.function(let f)) = program.declaration(referredToBy: n) {
        return f
      } else {
        return nil
      }
    }
  }

  /// If `e` is an inout-expression, returns its lvalue. Otherwise, returns `e`.
  private func sansMutationMarker(_ e: ExpressionIdentity) -> ExpressionIdentity {
    if let n = program.cast(e, to: InoutExpression.self) {
      return program[n].lvalue
    } else {
      return e
    }
  }

}
