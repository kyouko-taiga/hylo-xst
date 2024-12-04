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
    class A {}
    conformance A: P { typealias X = A }
    fun f(_ x: A.X) -> A { g(x) }
    fun g(_ x: A) { true }
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
