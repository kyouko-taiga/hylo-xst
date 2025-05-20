import FrontEnd

/// The translation of an intermediate representation to C++ using monomorphization.
public struct MonomorphizingRenderer {

  /// The IR being lowered.
  public internal(set) var ir: IRProgram

  /// The program containing the IR being rendered.
  public internal(set) var program: Program

  /// Creates an instance rendering `ir`, which lowers modules in `p`.
  public init(rendering ir: IRProgram, loweredFrom p: consuming Program) {
    self.ir = ir
    self.program = p
  }

  /// Renders `ir`.
  public mutating func apply() -> (header: String, source: String) {
    print(program.show(ir))

    var header = """
    #pragma once

    
    """

    var source = """
    #include "product.h"
    #include "xst.h"

    
    """

    for (_, f) in ir.functions {
      header.write(declaration(f))
      header.write(";\n")

      if let b = f.body {
        source.write(declaration(f))
        source.write(" {\n")
        source.write(render(body: b))
        source.write("}\n\n")
      }
    }

    return (header, source)
  }

  /// Returns the resources held by this instance.
  public consuming func release() -> Program {
    self.program
  }

  /// Returns C++ translation of the declaration of `d`.
  private mutating func declaration(_ f: IRFunction) -> String {
    var result = "void \(f.identifier.assemblySanitized) ("

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
        result.write("; ")
      }
      result.write(render(last))
    } else {
      result.write(render(t))
    }

    result.write(";")
    return result
  }

  /// Returns the C++ translation of `t`.
  private mutating func render(_ t: IRTree) -> String {
    switch t {
    case .bool(let b):
      return b ? "std::uint8_t{1}" : "std::uint8_t{0}"

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
      result.write("if (*static_cast<std::uint8_t*>(\(c))) ")
      result.write("{ return ")
      result.write(render(success))
      result.write("; } else { return ")
      result.write(render(failure))
      result.write("; }")
      result.write(" })()")
      return result

    case .field(let i, let source, let type):
      let m = ir.metatype(of: type, using: program)
      let s = render(source)
      return "xst::advance(\(s), \(m.offsets[i]))"

    case .load(let source, let type):
      let s = render(source)
      return "*(static_cast<\(program.cpp(type))*>(\(s)))"

    case .nullptr:
      return "nullptr"

    case .copy(let target, let source, let type):
      let m = ir.metatype(of: type, using: program)
      let l = render(target)
      let r = render(source)
      return """
      std::memcpy(\(l), \(r), \(m.size));
      """

    case .discard(let source, _):
      let s = render(source)
      return """
      \(s);
      """

    case .return(let source, let type):
      let m = ir.metatype(of: type, using: program)
      let r = render(source)
      return """
      std::memcpy(x0, \(r), \(m.size));
      """

    case .store(let target, let source, let type):
      let l = render(target)
      let r = render(source)
      return """
      *(static_cast<\(program.cpp(type))*>(\(l))) = \(r);
      """

    case .variable(let n, let type):
      let m = ir.metatype(of: type, using: program)
      let x = ir.fresh()
      return """
      xst::AlignedBuffer<\(m.size), \(m.alignment)> \(x);
      void* \(n) = \(x).base_address();
      """

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

}

extension Program {

  /// Returns the name of the C++ type corresponding to `t`.
  fileprivate func cpp(_ t: MachineType.ID) -> String {
    switch types[t] {
    case .i(1):
      return "std::uint8_t"
    case .i(32):
      return "std::uint32_t"
    case .i(64):
      return "std::uint64_t"
    default:
      fatalError("unsupported type '\(show(t))'")
    }
  }

}
