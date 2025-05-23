import Archivist
import Utilities

/// The declaration of a trait.
@Archivable
public struct TraitDeclaration: TypeDeclaration, ModifiableDeclaration, Annotatable, Scope {

  /// The annotations on this declaration.
  public let annotations: [Annotation]

  /// The modifiers applied to this declaration.
  public let modifiers: [Parsed<DeclarationModifier>]

  /// The introducer of this declaration.
  public let introducer: Token

  /// The name of the declared trait.
  public let identifier: Parsed<String>

  /// The generic parameters of the trait.
  public let parameters: [GenericParameterDeclaration.ID]

  /// The members of the declared trait.
  public let members: [DeclarationIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    annotations: [Annotation],
    modifiers: [Parsed<DeclarationModifier>],
    introducer: Token,
    identifier: Parsed<String>,
    parameters: [GenericParameterDeclaration.ID],
    members: [DeclarationIdentity],
    site: SourceSpan
  ) {
    self.annotations = annotations
    self.modifiers = modifiers
    self.introducer = introducer
    self.identifier = identifier
    self.parameters = parameters
    self.members = members
    self.site = site
  }

}

extension TraitDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = ""
    for m in modifiers { result.append("\(m) ") }
    result.append("trait \(identifier.value)")

    if !parameters.isEmpty {
      result.append("<\(printer.show(parameters))>")
    }

    result.append(" {\n")
    for m in members { result.append(printer.show(m).indented + "\n") }
    result.append("}")

    return result
  }

}
