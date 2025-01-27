/// A trait.
public struct Trait: TypeTree {

  /// The declaration introducing this type.
  public let declaration: TraitDeclaration.ID

  /// Properties about `self`.
  public var properties: ValueProperties {
    .init()
  }

}

extension Trait: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    printer.program[declaration].identifier.value
  }

}

