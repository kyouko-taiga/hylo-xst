/// The type of a namespace.
public struct Namespace: TypeTree {

  /// The identifier of a namespace.
  public enum Identifier: Hashable, Sendable {

    /// The built-in module
    case builtin

    /// A module.
    case module(Program.ModuleIdentity)

  }

  /// The unique identifier of the namespace.
  public let identifier: Identifier

  /// Properties about `self`.
  public var properties: ValueProperties {
    .init()
  }

}

extension Namespace: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    printer.show(identifier)
  }

}

extension Namespace.Identifier: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    switch self {
    case .builtin:
      return "Builtin"
    case .module(let m):
      return printer.program[m].name.rawValue
    }
  }

}
