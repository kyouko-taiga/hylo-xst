import Archivist
import Foundation
import FrontEnd

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

    extension Int {}

    fun g(a: A) { true }
    """
  let s2: SourceFile = """
    trait R { type B }
    fun f(a b, , d: true) { false }
    """

  var program = Program()
  let m = program.demandIdentity(module: "org.hylo.Test")
  _ = program[m].addSource(s1)
  _ = program[m].addSource(s2)

  var o = ""
  for d in program[m].diagnostics.elements {
    d.render(
      into: &o, showingPaths: .relative(to: FileManager.default.currentDirectoryURL),
      style: .unstyled)
  }
  print(o)

  await program.assignScopes(m)
  program.assignTypes(m)

  for n in program.select(.kind(FunctionDeclaration.self)) {
    print(program.show(n))
  }

}

try await main()
