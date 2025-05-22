import FrontEnd
import OrderedCollections
import Utilities

/// The translation of an intermediate representation to C++ using monomorphization.
public struct MonomorphizingRenderer {

  /// A request to monomorphize a generic function for a given list of type arguments.
  private struct MonomorphizationRequest: Hashable {

    /// The identifier of the IR function to monomorphize.
    let symbol: String

    /// The type arguments for which the function should be monomorphized.
    let arguments: TypeArguments

  }

  /// The IR being lowered.
  public internal(set) var ir: IRProgram

  /// The program containing the IR being rendered.
  public internal(set) var program: Program

  /// A table from the types whose metadata have been requested during the rendering to the name
  /// of their constructor in the rendered program.
  private var requestedMetadata: OrderedDictionary<AnyTypeIdentity, String> = [:]

  private var requestedMonomorphizations: [MonomorphizationRequest] = []

  /// Creates an instance rendering `ir`, which lowers modules in `p`.
  public init(rendering ir: IRProgram, loweredFrom p: consuming Program) {
    self.ir = ir
    self.program = p
  }

  /// Renders `ir`.
  public mutating func apply() -> String {
    var declarations = ""
    var definitions = ""

    func _render(_ f: IRFunction) {
      assert(program.types[f.type] is Arrow)

      declarations.write(declaration(f))
      declarations.write(";\n")

      if let b = f.body {
        definitions.write(declaration(f))
        definitions.write(" {\n")
        definitions.write(render(body: b))
        definitions.write("}\n\n")
      }
    }

    // Render non-generic functions.
    for (_, f) in ir.functions where program.types[f.type] is Arrow {
      _render(f)
    }

    // Render monomorphized functions.
    var done: Set<MonomorphizationRequest> = []
    while let request = requestedMonomorphizations.popLast() {
      if !done.insert(request).inserted { continue }
      let n = monomorphize(request)
      _render(ir.functions[n]!)
    }

    return """
    #include "TypeStore.h"

    namespace rt {
    static xst::TypeStore store;
    \(renderRequestedMetadataConstructors())
    }

    // Forward declarations.
    \(declarations)
    // Definitions.
    \(definitions)
    """
  }

  /// Returns the resources held by this instance.
  public consuming func release() -> Program {
    self.program
  }

  /// Returns C++ translation of the declaration of `d`.
  private mutating func declaration(_ f: IRFunction) -> String {
    var result = "void \(f.identifier.assemblySanitized)("

    // First parameter is the storage of the return value.
    result.write("void* x0")
    for p in program[f.declaration].parameters {
      let n = ir.identifier(of: p, using: program).assemblySanitized
      result.write(", void* \(n)")
    }

    result.write(")")
    return result
  }

  /// Returns the C++ translation of `t`, which is the body of a function.
  private mutating func render(body t: IRTree) -> String {
    var result = ""

    if case .block(let prefix, let last) = t {
      for t in prefix {
        result.write(render(t))
        result.write(";\n")
      }
      result.write(render(last))
    } else {
      result.write(render(t))
    }

    result.write(";\n")
    return result
  }

  /// Returns the C++ translation of `t`.
  private mutating func render(_ t: IRTree) -> String {
    switch t {
    case .bool(let b):
      return b ? "std::int8_t{1}" : "std::int8_t{0}"

    case .builtinCall(let callee, let arguments):
      return render(apply: callee, to: arguments)

    case .block(let prefix, let last):
      var result = "([&](){ "
      for t in prefix {
        result.write(render(t))
        result.write("; ")
      }
      result.write("return ")
      result.write(render(last))
      result.write("; })()")
      return result

    case .call(let callee, let arguments):
      let f = render(callee)
      let a = arguments.map({ (x) in render(x) }).joined(separator: ", ")
      return "\(f)(\(a))"

    case .identifier(let n):
      return n.assemblySanitized

    case .if(let condition, let success, let failure):
      var result = "([&](){ "
      let c = render(condition)
      result.write("if (*static_cast<std::int8_t*>(\(c))) ")
      result.write("{ return ")
      result.write(render(success))
      result.write("; } else { return ")
      result.write(render(failure))
      result.write("; }")
      result.write(" })()")
      return result

    case .field(let i, let source, let type):
      let m = demandMetadata(of: type).name
      return "rt::store.address_of(rt::\(m)(), \(i), \(render(source)))"

    case .load(let source, let type):
      let s = render(source)
      return "*(static_cast<\(program.cpp(type))*>(\(s)))"

    case .nullptr:
      return "nullptr"

    case .typeApplication(let abstraction, let arguments):
      guard case .identifier(let n) = abstraction else {
        fatalError("unsupported expression '\(program.show(t))'")
      }
      requestedMonomorphizations.append(.init(symbol: n, arguments: arguments))
      return (n + suffix(for: arguments)).assemblySanitized

    case .copy(let target, let source, let type):
      let m = demandMetadata(of: type).name
      let l = render(target)
      let r = render(source)
      return "rt::store.copy_initialize(rt::\(m)(), \(l), \(r))"

    case .discard(let source, let type):
      let m = demandMetadata(of: type).name
      return "rt::store.deinitialize(rt::\(m)(), \(render(source)))"

    case .return(let source, let type):
      let m = demandMetadata(of: type).name
      return "rt::store.copy_initialize(rt::\(m)(), x0, \(render(source)))"

    case .store(let target, let source, let type):
      let m = demandMetadata(of: type.erased).name
      let l = render(target)
      let r = render(source)
      return "rt::store.copy_initialize_builtin(rt::\(m)(), \(l), \(r))"

    case .variable(let n, let type):
      let m = ir.store.metadata(of: type, appliedTo: .init(), using: &program)
      let s = ir.store.size(of: m)
      let a = ir.store.alignment(of: m)
      return "alignas(\(a)) std::byte \(n)[\(s)] = {}"
//      let m = demandMetatype(of: type.erased).name
//      let x = ir.fresh()
//      return """
//      auto \(x) = rt::\(m)();
//      auto \(n) = xst::aligned_alloc(rt::store.size(\(x)), rt::store.alignment(\(x)))
//      """

    case .void:
      return ";"
    }
  }

  /// Returns the C++ translation of `f` applied ro `a`.
  private mutating func render(apply f: BuiltinFunction, to a: [IRTree]) -> String {
    let arguments = a.map({ (x) in render(x) })
    switch f {
    case .zeroinitializer(let m):
      assert(a.isEmpty)
      return "\(program.cpp(m)){}"

    case .icmp(.eq, _):
      assert(a.count == 2)
      return "(\(arguments[0]) == \(arguments[1]))"

    default:
      fatalError("unsupported function '\(program.show(f))'")
    }
  }

  /// Returns the C++ translation of the metadata constructors for all the types whose metadata
  /// have been requested to during rendering.
  private mutating func renderRequestedMetadataConstructors() -> String {
    // The first element is for forward declarations.
    var results = [""]

    var work = requestedMetadata.elements.map { (e) in
      (name: e.value, type: e.key, arguments: TypeArguments())
    }

    func demand(_ t: AnyTypeIdentity, _ a: TypeArguments) -> String {
      let (inserted, n) = demandMetadata(of: t)
      if inserted { work.append((n, t, a)) }
      return n
    }

    while let (n, t, a) = work.popLast() {
      switch program.types[t] {
      case let u as MachineType:
        assert(a.isEmpty)
        results[0].write("""
          inline xst::BuiltinHeader const* \(n)(bool no_define = false) {
            return rt::store.declare(xst::BuiltinHeader::\(u));
          }\n
          """)

      case let u as Struct:
        let name = program.name(of: u.declaration)

        var fs: [String] = []
        for f in program.storedProperties(of: u.declaration) {
          let i = program.isIndirect(f)
          let u = program.typeSansEffect(assignedTo: f)
          let v = program.types.substitute(a, in: u)
          let n = demand(v, .init())
          fs.append("xst::Field{\(n)(\(i)), \(i)}")
        }

        var signature = "xst::StructHeader const* \(n)("
        var ps: [String] = []
        for i in 0 ..< program[u.declaration].staticParameters.explicit.count {
          ps.append("T\(i)")
          signature.write("xst::TypeHeader const* T\(i), ")
        }
        signature.write("bool no_define")

        results[0].write(signature + " = false);\n")
        results.append(
          """
          /// \(program.show(t))
          \(signature)) {
            auto h = store.declare(xst::StructHeader("\(name)", {\(list: ps)}));
            if (!no_define && !store.defined(h)) {
              store.define(h, {\(fs.joined(separator: ", "))});
            }
            return h;
          }
          """)

      case let u as TypeApplication:
        let f = demand(u.abstraction, u.arguments)
        let a = u.arguments.values.map({ (v) in demand(v, .init()) + "()" })
        results[0].write("xst::TypeHeader const* \(n)(bool no_define = false);\n")
        results.append(
          """
          /// \(program.show(t))
          xst::TypeHeader const* \(n)(bool no_define) {
            return \(f)(\(list: a), no_define);
          }
          """
        )

      default:
        fatalError("unsupported type '\(program.show(t))'")
      }
    }

    return results.joined(separator: "\n")
  }

  /// Returns the identifier of the function computing the metadata of `t` at runtime.
  private mutating func demandMetadata(of t: AnyTypeIdentity) -> (inserted: Bool, name: String) {
    if let x = requestedMetadata[t] {
      return (false, x)
    } else {
      let x = ir.fresh()
      requestedMetadata[t] = x
      return (true, x)
    }
  }

  /// Returns a suffix uniquely identifying the given `arguments`.
  private func suffix(for arguments: TypeArguments) -> String {
    arguments.values.reduce(into: "") { (s, t) in
      s.write(String(t.bits, radix: 36))
    }
  }

  /// Returns the identifier of the function satisfying the given monomorphization request.
  private mutating func monomorphize(
    _ request: MonomorphizationRequest
  ) -> String {
    let f = ir.functions[request.symbol] ?? fatalError("unknown IR function '\(request.symbol)'")
    let t = program.types[f.type] as! UniversalType
    let u = program.types.substitute(request.arguments, in: t.body)

    let s = suffix(for: request.arguments)
    let n = ir.declare(
      function: f.identifier + s, of: u, notionallyDeclaredBy: f.declaration, using: program)

    if let b = f.body {
      let monomorphized = monomorphize(b, for: request.arguments)
      ir.define(function: n, body: monomorphized)
    }

    return n
  }

  private mutating func monomorphize<S: Sequence<IRTree>>(
    _ ts: S, for a: TypeArguments
  ) -> [IRTree] {
    ts.map({ (t) in monomorphize(t, for: a) })
  }

  private mutating func monomorphize(_ t: IRTree, for a: TypeArguments) -> IRTree {
    switch t {
    case .bool:
      return t

    case .builtinCall(let callee, let arguments):
      let x0 = monomorphize(arguments, for: a)
      return .builtinCall(callee, x0)

    case .block(let prefix, let last):
      let x0 = monomorphize(prefix, for: a)
      let x1 = monomorphize(last, for: a)
      return .block(prefix: x0, last: x1)

    case .call(let callee, let arguments):
      let x0 = monomorphize(callee, for: a)
      let x1 = monomorphize(arguments, for: a)
      return .call(x0, x1)

    case .identifier:
      return t

    case .if(let condition, let success, let failure):
      let x0 = monomorphize(condition, for: a)
      let x1 = monomorphize(success, for: a)
      let x2 = monomorphize(failure, for: a)
      return .if(x0, then: x1, else: x2)

    case .field(let i, let source, let type):
      let x0 = monomorphize(source, for: a)
      let t0 = program.types.substitute(a, in: type)
      return .field(i, source: x0, type: t0)

    case .load(let source, let type):
      let x0 = monomorphize(source, for: a)
      return .load(source: x0, type: type)

    case .nullptr:
      return t

    case .typeApplication(let abstraction, let arguments):
      guard case .identifier(let n) = abstraction else {
        fatalError("unsupported expression '\(program.show(t))'")
      }
      let b = arguments.mapValues({ (u) in program.types.substitute(a, in: u) })
      requestedMonomorphizations.append(.init(symbol: n, arguments: b))
      return .identifier(n + suffix(for: b))

    case .copy(let target, let source, let type):
      let x0 = monomorphize(target, for: a)
      let x1 = monomorphize(source, for: a)
      let t0 = program.types.substitute(a, in: type)
      return .copy(target: x0, source: x1, type: t0)

    case .discard(let source, let type):
      let x0 = monomorphize(source, for: a)
      let t0 = program.types.substitute(a, in: type)
      return .discard(source: x0, type: t0)

    case .return(let source, let type):
      let x0 = monomorphize(source, for: a)
      let t0 = program.types.substitute(a, in: type)
      return .return(source: x0, type: t0)

    case .store(let target, let source, let type):
      let x0 = monomorphize(target, for: a)
      let x1 = monomorphize(source, for: a)
      return .store(target: x0, source: x1, type: type)

    case .variable(let n, let type):
      let t0 = program.types.substitute(a, in: type)
      return .variable(identifier: n, type: t0)

    case .void:
      return t
    }
  }

}
