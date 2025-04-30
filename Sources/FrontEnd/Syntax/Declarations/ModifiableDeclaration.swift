/// A declaration that may have modifiers.
public protocol ModifiableDeclaration: Declaration {

  /// The modifiers applied to this declaration.
  var modifiers: [Parsed<DeclarationModifier>] { get }

}

extension ModifiableDeclaration {

  /// Returns `true` iff `self` has the given declaration modifier.
  public func `is`(_ modifier: DeclarationModifier) -> Bool {
    modifiers.contains(where: { (m) in m.value == modifier })
  }

}
