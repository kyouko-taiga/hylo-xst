import Utilities

/// The application of a type abstraction.
public struct TypeApplication: TypeTree {

  /// The abstraction being applied.
  public var abstraction: AnyTypeIdentity

  /// The arguments of the application.
  public var arguments: [Value]

  /// Properties about `self`.
  public var properties: ValueProperties {
    .notCanonical
  }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    "\(program.show(abstraction))<\(list: arguments.map(program.show(_:)))>"
  }

}
