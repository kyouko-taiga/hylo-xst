import Archivist
import Utilities

/// The declaration of a function.
public struct FunctionDeclaration: Declaration & Scope {

  /// The identifier of a function.
  public enum Identifier: Equatable {

    /// A simple identifier.
    case simple(String)

    /// An operator with its notation.
    case `operator`(OperatorNotation, String)

  }

  /// The introducer of this declaration.
  public let introducer: Token

  /// The name of the declared trait.
  public let identifier: Parsed<Identifier>

  /// The declarations of the function's parameters.
  public let parameters: [ParameterDeclaration.ID]

  /// The body of the function.
  public let body: CallableBody?

  /// The site from which `self` was parsed.
  public var site: SourceSpan

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    var result = "fun \(identifier)(\(list: parameters.map(program.show(_:))))"

    switch body {
    case .some(.expression(let n)):
      let e = program.show(n).indented
      result.append(" {\n\(e)\n}")
    case nil:
      break
    }

    return result
  }

}

extension FunctionDeclaration.Identifier: CustomStringConvertible {

  public var description: String {
    switch self {
    case .simple(let s):
      return s
    case .operator(let n, let s):
      return "\(n)\(s)"
    }
  }

}

extension FunctionDeclaration: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    fatalError()
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    fatalError()
  }

}
