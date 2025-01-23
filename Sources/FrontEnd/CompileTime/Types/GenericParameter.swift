import Utilities

/// A generic parameter.
public enum GenericParameter: TypeTree {

  case reflexivity

  case symmetry(UInt8)

  case transitivity(UInt8)

  case user(GenericParameterDeclaration.ID)

  // Properties about `self`.
  public var properties: ValueProperties {
    .init()
  }

  /// The declaration of the parameter, unless it is predefined.
  public var declaration: GenericParameterDeclaration.ID? {
    if case .user(let d) = self { d } else { nil }
  }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    switch self {
    case .reflexivity:
      return "T"
    case .symmetry(let i):
      return "T\(i)"
    case .transitivity(let i):
      return "T\(i)"
    case .user(let d):
      return program[d].identifier.value
    }
  }

}
