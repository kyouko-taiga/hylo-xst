import Archivist
import Utilities

/// The declaration of a function.
public struct FunctionDeclaration: Declaration, Scope {

  /// The introducer of an initializer declaration.
  public enum Introducer: UInt8 {

    /// The function introducer, `fun`.
    case fun

    /// The initializer introducer, `init`.
    case `init`

    /// The memberwise initializer introducer, `memberwise init`
    case memberwiseinit

  }

  /// The identifier of a function.
  public enum Identifier: Equatable {

    /// A simple identifier.
    case simple(String)

    /// An operator with its notation.
    case `operator`(OperatorNotation, String)

  }

  /// The introducer of this declaration.
  public let introducer: Parsed<Introducer>

  /// The name of the declared function.
  public let identifier: Parsed<Identifier>

  /// The compile-time parameters of the function.
  public let staticParameters: StaticParameters

  /// The run-time parameters of the function.
  public let parameters: [ParameterDeclaration.ID]

  /// The effect of the function's call operator.
  public let effect: Parsed<AccessEffect>

  /// The type of the function's return value.
  public let output: ExpressionIdentity?

  /// The body of the function.
  public let body: [StatementIdentity]?

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// `true` iff `self` declares a memberwise initializer.
  public var isMemberwiseInitializer: Bool {
    introducer.value == .memberwiseinit
  }

}

extension FunctionDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result: String = ""

    switch introducer.value {
    case .fun: result.append("fun \(identifier.value)")
    case .`init`: result.append("init")
    case .memberwiseinit: result.append("memberwise init")
    }

    if !staticParameters.isEmpty {
      result.append(printer.show(staticParameters))
    }

    result.append("(")
    result.append(printer.show(parameters))
    result.append(")")

    if introducer.value == .fun {
      result.append(" \(effect.value) -> " + (output.map({ (o) in printer.show(o) }) ?? "Void"))
    }

    if let b = body {
      result.append(" {\n")
      for s in b { result.append(printer.show(s).indented + "\n") }
      result.append("}")
    }

    return result
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
