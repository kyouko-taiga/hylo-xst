import Archivist

/// A struct.
@Archivable
public struct Struct: TypeTree {

  /// The declaration introducing this type.
  public let declaration: StructDeclaration.ID

  /// Creates an instance with the given properties.
  public init(declaration: StructDeclaration.ID) {
    self.declaration = declaration
  }

  /// Properties about `self`.
  public var properties: ValueProperties {
    .init()
  }

}

extension Struct: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    printer.program[declaration].identifier.value
  }

}
