import Archivist

/// The declaration of a structure.
@Archivable
public struct StructDeclaration: TypeDeclaration, Scope {

  /// The modifiers applied to this declaration.
  public let modifiers: [Parsed<DeclarationModifier>]

  /// The introducer of this declaration.
  public let introducer: Token

  /// The name of the declared struct.
  public let identifier: Parsed<String>

  /// The compile-time parameters of the struct.
  public let staticParameters: StaticParameters

  /// The conformances declared along with the struct.
  public let contextBounds: [ConformanceDeclaration.ID]

  /// The members of the declared struct.
  public let members: [DeclarationIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    modifiers: [Parsed<DeclarationModifier>],
    introducer: Token,
    identifier: Parsed<String>,
    staticParameters: StaticParameters,
    contextBounds: [ConformanceDeclaration.ID],
    members: [DeclarationIdentity],
    site: SourceSpan
  ) {
    self.modifiers = modifiers
    self.introducer = introducer
    self.identifier = identifier
    self.staticParameters = staticParameters
    self.contextBounds = contextBounds
    self.members = members
    self.site = site
  }

}

extension StructDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = ""
    for m in modifiers { result.append("\(m) ") }
    result.append("struct \(identifier.value)")

    if !staticParameters.isEmpty {
      result.append(printer.show(staticParameters))
    }
    if !contextBounds.isEmpty {
      result.append(": ")
      result.append(printer.show(contextBounds, separatedBy: " & "))
    }

    result.append(" {\n")
    for m in members { result.append(printer.show(m).indented + "\n") }
    result.append("}")

    return result
  }

}
