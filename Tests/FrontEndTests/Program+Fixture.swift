import FrontEnd

extension Program {

  /// A test program.
  static var test: Program {
    var p = Program()

    let m0 = p.demandIdentity(module: "org.hylo.M0")
    _ = p[m0].addSource("""
      trait P { type X }
      """)
    _ = p[m0].addSource("""
      trait Q { type Y }
      """)

    let m1 = p.demandIdentity(module: "org.hylo.M1")
    p[m1].addDependency(p[m0].name)
    _ = p[m1].addSource("""
      trait R { type Z }
      """)

    let m2 = p.demandIdentity(module: "org.hylo.M2")
    p[m2].addDependency(p[m0].name)
    _ = p[m2].addSource("""
      trait R { type Z }
      """)

    return p
  }

  /// Returns `self` with the scoping relationships computed.
  func scoped() async -> Self {
    var q = self
    for m in moduleIdentities {
      await q.assignScopes(m)
    }
    return q
  }

}
