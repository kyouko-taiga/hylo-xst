import Algorithms
import FrontEnd

/// The intermediate representation of an expression.
public indirect enum IRTree: Hashable {

  // MARK: Expressions

  /// A non-empty sequence of trees.
  case block(prefix: [IRTree], last: IRTree)

  /// A call to a built-in function.
  case builtinCall(BuiltinFunction, arguments: [IRTree])

  /// A function call.
  case call(IRTree, [IRTree])

  /// The selection of the `i`-th field of the instance of `type` stored at `source`.
  case field(_ i: Int, source: IRTree, type: AnyTypeIdentity)

  /// An identifier.
  case identifier(String)

  /// A conditional expression.
  case `if`(IRTree, then: IRTree, else: IRTree)

  /// The dereferencing of a pointer.
  case load(source: IRTree, type: MachineType.ID)

  /// The null pointer.
  case nullptr

  // MARK: Statements

  /// A copy of the instance of `type` stored at `source` to `target`.
  case copy(target: IRTree, source: IRTree, type: AnyTypeIdentity)

  /// The deinitialization of theinstance of `type` stored at `source`.
  case discard(source: IRTree, type: AnyTypeIdentity)

  /// A copy of the instance of `type` stored at `source` to the result of the function.
  case `return`(source: IRTree, type: AnyTypeIdentity)

  /// A copy of `source`, which is an instance of `type`, to `target`.
  case store(target: IRTree, source: IRTree, type: MachineType.ID)

  /// The declaration of a local variable.
  case variable(identifier: String, type: AnyTypeIdentity)

  /// An empty statement.
  case void

  // MARK: Helpers

  /// Returns `trees` as a block if it contains multiple elements or as a single tree otherwise.
  public init<T: Sequence<IRTree>>(_ trees: T) {
    let xs = Array(trees.filter({ (t) in t != .void }))
    switch xs.count {
    case 0:
      self = .void
    case 1:
      self = xs[0]
    default:
      var prefix: [IRTree] = xs.reduce(into: []) { (ys, t) in
        if case .block(let p, let l) = t {
          ys.append(contentsOf: p)
          ys.append(l)
        } else {
          ys.append(t)
        }
      }
      let last = prefix.removeLast()
      self = .block(prefix: prefix, last: last)
    }
  }

  /// `true` iff `self` is `.builtinCall`.
  public var isBuiltinCall: Bool {
    if case .builtinCall = self { return true } else { return false }
  }

  /// `true` iff `self` is `.variable`.
  public var isVariable: Bool {
    if case .variable = self { return true } else { return false }
  }

  /// Returns `self` with variable declarations moved to the front.
  public var normalized: IRTree {
    var lhs: [IRTree] = []
    var rhs: [IRTree] = []

    switch self {
    case .block(let prefix, let last):
      for t in prefix {
        let (v, b) = t.variablesAndBody2
        lhs.append(contentsOf: v)
        rhs.append(b)
      }
      let l = last.variablesAndBody2
      lhs.append(contentsOf: l.variables)
      lhs.append(contentsOf: rhs)
      lhs.append(l.body)

    case .builtinCall(let callee, let arguments):
      for t in arguments {
        let (v, b) = t.variablesAndBody2
        lhs.append(contentsOf: v)
        rhs.append(b)
      }
      lhs.append(.builtinCall(callee, arguments: rhs))

    case .call(let callee, let arguments):
      let f = callee.variablesAndBody2
      lhs.append(contentsOf: f.variables)
      for t in arguments {
        let (v, b) = t.variablesAndBody2
        lhs.append(contentsOf: v)
        rhs.append(b)
      }
      lhs.append(.call(f.body, rhs))

    case .field(let i, let source, let type):
      let (v, b) = source.variablesAndBody2
      lhs.append(contentsOf: v)
      lhs.append(.field(i, source: b, type: type))

    case .identifier:
      return self

    case .if(let condition, let success, let failure):
      let c = condition.variablesAndBody2
      lhs.append(contentsOf: c.variables)
      let s = success.variablesAndBody2
      lhs.append(contentsOf: s.variables)
      let f = failure.variablesAndBody2
      lhs.append(contentsOf: f.variables)
      lhs.append(.if(c.body, then: s.body, else: f.body))

    case .load(let source, let type):
      let (v, b) = source.variablesAndBody2
      lhs.append(contentsOf: v)
      lhs.append(.load(source: b, type: type))

    case .nullptr:
      return self

    case .copy(let target, let source, let type):
      let l = target.variablesAndBody2
      lhs.append(contentsOf: l.variables)
      let r = source.variablesAndBody2
      lhs.append(contentsOf: r.variables)
      lhs.append(.copy(target: l.body, source: r.body, type: type))

    case .discard(let source, let type):
      let (v, b) = source.variablesAndBody2
      lhs.append(contentsOf: v)
      lhs.append(.discard(source: b, type:type))

    case .return(let source, let type):
      let r = source.variablesAndBody2
      lhs.append(contentsOf: r.variables)
      lhs.append(.return(source: r.body, type: type))

    case .store(let target, let source, let type):
      let l = target.variablesAndBody2
      lhs.append(contentsOf: l.variables)
      let r = source.variablesAndBody2
      lhs.append(contentsOf: r.variables)
      lhs.append(.store(target: l.body, source: r.body, type: type))

    case .variable:
      return self

    case .void:
      return self
    }

    return .init(lhs)
  }

  private var variablesAndBody2: (variables: [IRTree], body: IRTree) {
    switch self.normalized {
    case .block(let p, let l):
      let i = p.firstIndex(where: { (t) in !t.isVariable }) ?? p.endIndex
      return (Array(p[..<i]), IRTree(p[i...] + [l]))
    case .variable:
      return ([self], .void)
    default:
      return ([], self)
    }
  }

  /// If `self` is a normalized block, returns its variables and the rest of its trees. Otherwise,
  /// returns an empty array and `self`.
  private var variablesAndBody: (variables: [IRTree], body: IRTree) {
    if case .block(let p, let l) = self {
      let i = p.firstIndex(where: { (t) in !t.isVariable }) ?? p.endIndex
      return (Array(p[..<i]), IRTree(p[i...] + [l]))
    } else {
      return ([], self)
    }
  }

}

extension IRTree: Showable {

  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .block(let p, let l):
      return "{\((p + [l]).map({ (t) in printer.show(t) }).joined(separator: "; "))}"
    case .builtinCall(let f, let a):
      return "\(printer.show(f))(\(printer.show(a)))"
    case .call(let f, let a):
      return "\(printer.show(f))(\(printer.show(a)))"
    case .field(let i, let s, _):
      return "\(printer.show(s))[\(i)]"
    case .identifier(let n):
      return n
    case .if(let c, let t, let e):
      return "if(\(printer.show(c)) then \(printer.show(t)) else \(printer.show(e))"
    case .load(let s, _):
      return "load(\(printer.show(s)))"
    case .nullptr:
      return "nullptr"

    case .copy(let t, let s, _):
      return "copy(\(printer.show(t)), \(printer.show(s)))"
    case .discard(let s, _):
      return "discard(\(printer.show(s))"
    case .return(let s, _):
      return "return(\(printer.show(s)))"
    case .store(let t, let s, _):
      return "store(\(printer.show(t)), \(printer.show(s)))"
    case .variable(let n, let t):
      return "var \(n) : \(printer.show(t))"
    case .void:
      return "void"
    }
  }

}
