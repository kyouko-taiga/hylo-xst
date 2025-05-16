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

  /// Returns `self` with its variables moved to the front and its sub-expressions flattened.
  public var normalized: IRTree {
    .init(self.flattened)
  }

  /// Returns `self` flattened as a sequence of trees that, if evaluated in order, has the same
  /// semantics has `self`.
  private var flattened: [IRTree] {
    var xs: [IRTree] = []

    switch self {
    case .block(let prefix, let last):
      var ys: [IRTree] = []
      for t in prefix + [last] {
        let zs = t.flattened
        let i = zs.firstIndex(where: { (u) in !u.isVariable }) ?? zs.endIndex
        xs.append(contentsOf: zs[..<i])
        ys.append(contentsOf: zs[i...])
      }
      xs.append(contentsOf: ys)

    case .builtinCall(let callee, let arguments):
      let (ys, zs) = Self.flatten(expressions: arguments)
      xs = ys
      xs.append(.builtinCall(callee, arguments: zs))

    case .call(let callee, let arguments):
      let (ys, zs) = Self.flatten(expressions: arguments.prepended(with: callee))
      xs = ys
      xs.append(.call(zs[0], Array(zs[1...])))

    case .field(let i, let source, let type):
      let zs = source.flattened
      xs = zs.dropLast()
      xs.append(.field(i, source: zs.last!, type: type))

    case .identifier:
      return [self]

    case .if(let condition, let success, let failure):
      let zs = condition.flattened.partitioned(by: \.isVariable)
      xs.append(contentsOf: zs.trueElements)
      let ss = success.flattened.partitioned(by: \.isVariable)
      xs.append(contentsOf: ss.trueElements)
      let fs = failure.flattened.partitioned(by: \.isVariable)
      xs.append(contentsOf: fs.trueElements)
      xs.append(contentsOf: zs.falseElements.dropLast())
      xs.append(
        .if(zs.falseElements.last!, then: .init(ss.falseElements), else: .init(fs.falseElements)))

    case .load(let source, let type):
      let zs = source.flattened
      xs = zs.dropLast()
      xs.append(.load(source: zs.last!, type: type))

    case .nullptr:
      return [self]

    case .copy(let target, let source, let type):
      let (ys, zs) = Self.flatten(expressions: [target, source])
      xs.append(contentsOf: ys)
      xs.append(.copy(target: zs[0], source: zs[1], type: type))

    case .discard(let source, let type):
      let zs = source.flattened
      xs = zs.dropLast()
      xs.append(.discard(source: zs.last!, type: type))

    case .return(let source, let type):
      let zs = source.flattened
      xs = zs.dropLast()
      xs.append(.return(source: zs.last!, type: type))

    case .store(let target, let source, let type):
      let (ys, zs) = Self.flatten(expressions: [target, source])
      xs.append(contentsOf: ys)
      xs.append(.store(target: zs[0], source: zs[1], type: type))

    case .variable:
      xs = [self]

    case .void:
      xs = [self]
    }

    return xs
  }

  /// Returns a pair whose first element contains the flattened representations of `expressions` in
  /// order sans their last sub-expressions, which are in the second element.
  private static func flatten<S: Sequence<IRTree>>(
    expressions: S
  ) -> (prefixes: [IRTree], lasts: [IRTree]) {
    var xs: [IRTree] = []
    var ys: [IRTree] = []
    var zs: [IRTree] = []

    for t in expressions {
      let us = t.flattened
      let i = us.firstIndex(where: { (u) in !u.isVariable })!
      xs.append(contentsOf: us[..<i])
      ys.append(contentsOf: us[i...].dropLast())
      zs.append(us.last!)
    }

    return (xs + ys, zs)
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
