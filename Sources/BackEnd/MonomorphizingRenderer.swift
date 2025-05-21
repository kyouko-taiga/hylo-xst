import FrontEnd
import OrderedCollections

/// The translation of an intermediate representation to C++ using monomorphization.
public struct MonomorphizingRenderer {

  /// The IR being lowered.
  public internal(set) var ir: IRProgram

  /// The program containing the IR being rendered.
  public internal(set) var program: Program

  /// A table from the types whose metatypes have been requested during the rendering to the name
  /// of their constructor in the rendered program.
  private var requestedMetatypes: OrderedDictionary<AnyTypeIdentity, String> = [:]

  /// Creates an instance rendering `ir`, which lowers modules in `p`.
  public init(rendering ir: IRProgram, loweredFrom p: consuming Program) {
    self.ir = ir
    self.program = p
  }

  /// Renders `ir`.
  public mutating func apply() -> String {
    var declarations = ""
    var definitions = ""

    for (_, f) in ir.functions {
      declarations.write(declaration(f))
      declarations.write(";\n")

      if let b = f.body {
        definitions.write(declaration(f))
        definitions.write(" {\n")
        definitions.write(render(body: b))
        definitions.write("}\n\n")
      }
    }

    return """
    #include "TypeStore.h"

    namespace rt {
    static xst::TypeStore store;
    \(renderRequestedMetatypes())
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

    case .call(.identifier(let callee), let arguments):
      let f = callee.assemblySanitized
      let a = arguments.map({ (x) in render(x) }).joined(separator: ", ")
      return "\(f)(\(a))"

    case .call(let f, _):
      fatalError("unsupported callee '\(program.show(f))'")

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
      let m = demandMetatype(of: type).name
      return "rt::store.address_of(rt::\(m)(), \(i), \(render(source)))"

    case .load(let source, let type):
      let s = render(source)
      return "*(static_cast<\(program.cpp(type))*>(\(s)))"

    case .nullptr:
      return "nullptr"

    case .copy(let target, let source, let type):
      let m = demandMetatype(of: type).name
      let l = render(target)
      let r = render(source)
      return "rt::store.copy_initialize(rt::\(m)(), \(l), \(r))"

    case .discard(let source, let type):
      let m = demandMetatype(of: type).name
      return "rt::store.deinitialize(rt::\(m)(), \(render(source)))"

    case .return(let source, let type):
      let m = demandMetatype(of: type).name
      return "rt::store.copy_initialize(rt::\(m)(), x0, \(render(source)))"

    case .store(let target, let source, let type):
      let m = demandMetatype(of: type.erased).name
      let l = render(target)
      let r = render(source)
      return "rt::store.copy_initialize_builtin(rt::\(m)(), \(l), \(r))"

    case .variable(let n, let type):
      let m = ir.metatype(of: type, using: program)
      return "alignas(\(m.alignment)) std::byte \(n)[\(m.size)] = {}"
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

  /// Returns the C++ translation of the metatype constructors for all the types whose metatypes
  /// have been requested to during rendering.
  private mutating func renderRequestedMetatypes() -> String {
    // The first element is for forward declarations.
    var results = [""]

    var work = Array(requestedMetatypes.elements)
    while let (t, n) = work.popLast() {
      // Emit the definition of the metatype constructor.
      switch program.types[t] {
      case let u as MachineType:
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
          let (inserted, n) = demandMetatype(of: u)
          if inserted {
            work.append((u, n))
          }
          fs.append("xst::Field{\(n)(\(i)), \(i)}")
        }

        results[0].write("xst::StructHeader const* \(n)(bool no_define = false);\n")
        results.append(
          """
          xst::StructHeader const* \(n)(bool no_define) {
            auto h = store.declare(xst::StructHeader("\(name)", {}));
            if (!no_define && !store.defined(h)) {
              store.define(h, {\(fs.joined(separator: ", "))});
            }
            return h;
          }
          """)

      default:
        fatalError("unsupported type '\(program.show(t))'")
      }
    }

    return results.joined(separator: "\n")
  }

  /// Returns the identifier of the function computing the metatype of `t` at runtime.
  private mutating func demandMetatype(of t: AnyTypeIdentity) -> (inserted: Bool, name: String) {
    if let x = requestedMetatypes[t] {
      return (false, x)
    } else {
      let x = ir.fresh()
      requestedMetatypes[t] = x
      return (true, x)
    }
  }

}

extension Program {

  /// Returns the name of the C++ type corresponding to `t`.
  fileprivate func cpp(_ t: MachineType.ID) -> String {
    switch types[t] {
    case .i(1):
      return "std::int8_t"
    case .i(32):
      return "std::uint32_t"
    case .i(64):
      return "std::uint64_t"
    default:
      fatalError("unsupported type '\(show(t))'")
    }
  }

}
