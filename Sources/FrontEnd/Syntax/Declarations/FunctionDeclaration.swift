import Archivist
import Utilities

/// The declaration of a function.
public struct FunctionDeclaration: Declaration, Scope {

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

  /// The type of the function's return value.
  public let output: ExpressionIdentity?

  /// The body of the function.
  public let body: [StatementIdentity]?

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    let i = parameters.map(program.show(_:)).descriptions()
    let o = output.map(program.show(_:)) ?? "Void"
    var result = "fun \(identifier)(\(i)) -> \(o)"

    if let b = body {
      result.append(" {\n")
      for s in b { result.append(program.show(s).indented + "\n") }
      result.append("}")
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
