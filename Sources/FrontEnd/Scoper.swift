/// A function computing the scoping relationships of a module.
public struct Scoper {

  /// Creates an instance.
  public init() {}

  /// Computes the scoping relationships in `m`, which is in `p`.
  public func visit(_ m: Program.ModuleIdentity, in p: inout Program) async {
    let ts = p[m].sources.values.indices.map { (i) in
      Task.detached { [p] in
        let f = Program.SourceFileIdentity(module: m, offset: i)
        var v = Visitor(p[f])
        for o in p[f].syntax.indices {
          let n = AnySyntaxIdentity(file: f, offset: o)
          p.visit(n, calling: &v)
        }
        return v
      }
    }

    for (i, t) in ts.enumerated() {
      let f = Program.SourceFileIdentity(module: m, offset: i)
      var v = await t.value
      swap(&p[f].syntaxToParent, &v.syntaxToParent)
      swap(&p[f].scopeToDeclarations, &v.scopeToDeclarations)
    }
  }

  /// The computation of the scoping relationships in a single source file.
  private struct Visitor: SyntaxVisitor {

    /// A table from syntax tree to the scope that contains it.
    var syntaxToParent: [Int]

    /// A table from scope to the declarations that it contains directly.
    var scopeToDeclarations: [Int: [DeclarationIdentity]]

    /// The innermost lexical scope currently visited.
    var innermost: Int

    /// Creates an instance for computing the relationships of `f`.
    init(_ f: Module.SourceContainer) {
      self.syntaxToParent = f.syntaxToParent
      self.scopeToDeclarations = [:]
      self.innermost = -1
    }

    mutating func willEnter(_ n: AnySyntaxIdentity, in program: Program) -> Bool {
      syntaxToParent[n.offset] = innermost
      if let m = program.castToDeclaration(n), innermost >= 0 {
        scopeToDeclarations[innermost]!.append(m)
      }
      if program.isScope(n) {
        innermost = n.offset
        scopeToDeclarations[innermost] = []
      }
      return true
    }

    mutating func willExit(_ n: AnySyntaxIdentity, in program: Program) {
      if program.isScope(n) {
        innermost = syntaxToParent[n.offset]
      }
    }

  }

}
