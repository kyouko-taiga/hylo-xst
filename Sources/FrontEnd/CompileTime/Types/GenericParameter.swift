import Utilities

/// A generic parameter.
public enum GenericParameter: TypeTree {

  /// The generic parameter of a built-in coercion given.
  case equality(EqualityProperty, UInt8)

  /// The generic parameter representing the conformer of a trait.
  case trait(TraitDeclaration.ID)

  /// A generic parameter declared in sources.
  case user(GenericParameterDeclaration.ID)

  /// Properties about `self`.
  public var properties: ValueProperties {
    .init()
  }

  /// The declaration of the parameter, unless it is predefined.
  public var declaration: GenericParameterDeclaration.ID? {
    if case .user(let d) = self { d } else { nil }
  }

}

extension GenericParameter: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .equality(_, let i):
      return printer.uniquized("T\(i)", for: self)
    case .trait:
      return printer.uniquized("Self", for: self)
    case .user(let d):
      return printer.uniquized(printer.program[d].identifier.value, for: self)
    }
  }

}
