/// A set of formulae to be proven for checking the type of a syntax tree.
internal struct Obligations {

  /// A table from syntax tree to its type.
  internal private(set) var syntaxToType: [AnySyntaxIdentity: AnyTypeIdentity]

  /// A table from name component to its declaration.
  internal private(set) var nameToDeclaration: [NameExpression.ID: DeclarationReference]

  /// `true` iff a this set cannot be discharged because.
  internal private(set) var isUnsatisfiable: Bool

  /// Creates an empty set.
  internal init() {
    syntaxToType = [:]
    nameToDeclaration = [:]
    isUnsatisfiable = false
  }

  /// Marks `self` to be unsatisfiable.
  internal mutating func setUnsatisfiable() {
    isUnsatisfiable = true
  }

  /// Assumes that `n` has type `t`.
  internal mutating func assume(_ n: AnySyntaxIdentity, instanceOf t: AnyTypeIdentity) {
    syntaxToType[n] = t
  }

  /// Assumes that `n` refers to `r`.
  internal mutating func assume(_ n: NameExpression.ID, isBoundTo r: DeclarationReference) {
    nameToDeclaration[n] = r
  }

}
