import OrderedCollections

/// A function computing the scoping relationships of a module.
public struct Scoper {

  /// Creates an instance.
  public init() {}

  /// Computes the scoping relationships in `m`, which is in `p`.
  public func visit(_ m: Program.ModuleIdentity, in p: inout Program) async {
    let ts = p[m].sources.values.indices.map { (f) in
      Task.detached { [p] in
        var v = Visitor(syntaxCount: p[m][f].syntax.count)
        for o in p[m][f].syntax.indices {
          let n = AnySyntaxIdentity(rawValue: .init(module: m, file: f, node: o))
          p.visit(n, calling: &v)
        }
        return v
      }
    }

    for (f, t) in ts.enumerated() {
      var v = await t.value
      swap(&p[m][f].syntaxToParent, &v.syntaxToParent)
      swap(&p[m][f].scopeToDeclarations, &v.scopeToDeclarations)
    }
  }

  /// The computation of the scoping relationships in a single source file.
  private struct Visitor: SyntaxVisitor {

    /// A table from syntax tree to the scope that contains it.
    var syntaxToParent: [Int]

    /// A table from scope to the declarations that it contains directly.
    var scopeToDeclarations: OrderedDictionary<Int, DeclarationSet>

    /// The innermost lexical scope currently visited.
    var innermost: Int

    /// Creates an instance for computing the relationships of a tree with `syntaxCount` nodes.
    init(syntaxCount: Int) {
      self.syntaxToParent = Array(repeating: -1, count: syntaxCount)
      self.scopeToDeclarations = [:]
      self.innermost = -1
    }

    mutating func willEnter(_ n: AnySyntaxIdentity, in program: Program) -> Bool {
      syntaxToParent[n.rawValue.node] = innermost
      if let m = program.castToDeclaration(n), innermost >= 0 {
        scopeToDeclarations[innermost]!.append(m)
      }
      if program.isScope(n) {
        innermost = n.rawValue.node
        scopeToDeclarations[innermost] = []
      }
      return true
    }

    mutating func willExit(_ n: AnySyntaxIdentity, in program: Program) {
      if program.isScope(n) {
        innermost = syntaxToParent[n.rawValue.node]
      }
    }

  }

}
