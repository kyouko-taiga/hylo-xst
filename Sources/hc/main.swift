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
    trait P { type X }
    struct A {
      memberwise init
      let m0 = () 
      // let m1: Self
    }

    fun g(_ x: A) -> A { A(m0: ()) }
    fun f(_ x: A.X) {
      _ = g(x)
      return g(x)
    }

    conformance A: P { typealias X = A }
    """
  let s2: SourceFile = """
    """

  var program = Program()
  let m = program.demandModule("org.hylo.Test")
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
