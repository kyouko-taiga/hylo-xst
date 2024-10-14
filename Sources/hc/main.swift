import Archivist
import Foundation
import FrontEnd

func render(_ ds: DiagnosticSet) {
  var o = ""
  for d in ds.elements {
    d.render(
      into: &o, showingPaths: .relative(to: FileManager.default.currentDirectoryURL),
      style: .unstyled)
  }
  print(o)
}

func main() async throws {
  let s1: SourceFile = """
    trait P {
      type A
      type Y
    }

    trait Q {}

    class A {
      class B {}
    }

    extension A.B {
      class C {}
    }
    // extension A.B.C.B {}

    // fun g(a: A) -> A { true }
    // fun h(a a1: A) { true }
    // fun i(_ b: A.B) { true }
    """
  let s2: SourceFile = """
    trait R { type B }
    // fun f(a b, , d: true) { false }
    class C {}
    fun j(_ b: A.B.C) { true }
    """

  var program = Program()
  let m = program.demandIdentity(module: "org.hylo.Test")
  _ = program[m].addSource(s1)
  _ = program[m].addSource(s2)

  if program[m].diagnostics.containsError {
    render(program[m].diagnostics)
    return
  }

  await program.assignScopes(m)
  program.assignTypes(m)

  for n in program.select(.kind(FunctionDeclaration.self)) {
    print(program.show(n))
  }

  if program[m].diagnostics.containsError {
    render(program[m].diagnostics)
    return
  }
}

try await main()
