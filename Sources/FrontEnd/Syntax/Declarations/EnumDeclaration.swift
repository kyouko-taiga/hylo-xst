import Archivist

/// The declaration of an enumeration.
@Archivable
public struct EnumDeclaration: TypeDeclaration, ModifiableDeclaration, Scope {

  /// The modifiers applied to this declaration.
  public let modifiers: [Parsed<DeclarationModifier>]

  /// The introducer of this declaration.
  public let introducer: Token

  /// The name of the declared struct.
  public let identifier: Parsed<String>

  /// The compile-time parameters of the struct.
  public let staticParameters: StaticParameters

  /// The raw representation of the enumeration, if any.
  public let representation: ExpressionIdentity?

  /// The conformances declared along with the struct.
  public let conformances: [ConformanceDeclaration.ID]

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
    representation: ExpressionIdentity?,
    conformances: [ConformanceDeclaration.ID],
    members: [DeclarationIdentity],
    site: SourceSpan
  ) {
    self.modifiers = modifiers
    self.introducer = introducer
    self.identifier = identifier
    self.staticParameters = staticParameters
    self.representation = representation
    self.conformances = conformances
    self.members = members
    self.site = site
  }

}

extension EnumDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = ""
    for m in modifiers { result.append("\(m) ") }
    result.append("enum \(identifier.value)")

    if !staticParameters.isEmpty {
      result.append(printer.show(staticParameters))
    }

    if let r = representation {
      result.append("(\(printer.show(r)))")
    }

    if !conformances.isEmpty {
      result.append(" is ")
      result.append(printer.showAdjunct(conformances))
    }

    result.append(" {\n")
    for m in members { result.append(printer.show(m).indented + "\n") }
    result.append("}")

    return result
  }

}
