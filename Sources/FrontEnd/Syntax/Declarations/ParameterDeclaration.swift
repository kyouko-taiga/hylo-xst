import Archivist

/// The declaration of a function or subscript parameter.
@Archivable
public struct ParameterDeclaration: Declaration, Sendable {

  /// The label of the parameter.
  public let label: Parsed<String>?

  /// The identifier of the parameter.
  public let identifier: Parsed<String>

  /// The type ascription of the parameter, if any.
  public let ascription: RemoteTypeExpression.ID?

  /// The default value of the parameter, if any.
  public let defaultValue: ExpressionIdentity?

  /// The modifier specifying that the parameter is lazy, if any.
  public let lazyModifier: Token?

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(
    label: Parsed<String>?,
    identifier: Parsed<String>,
    ascription: RemoteTypeExpression.ID?,
    defaultValue: ExpressionIdentity?,
    lazyModifier: Token?,
    site: SourceSpan
  ) {
    assert((lazyModifier == nil) || (ascription != nil))
    self.label = label
    self.identifier = identifier
    self.ascription = ascription
    self.defaultValue = defaultValue
    self.lazyModifier = lazyModifier
    self.site = site
  }

}

extension ParameterDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = ""

    // Label and identifier.
    switch label {
    case .some(let l) where l.value == identifier.value:
      result.append(identifier.value)
    case .some(let l):
      result.append("\(l) \(identifier.value)")
    case nil:
      result.append("_ \(identifier.value)")
    }

    // Ascription.
    if let a = ascription {
      if lazyModifier == nil {
        result.append(": \(printer.show(a))")
      } else {
        result.append(": lazy \(printer.show(a))")
      }
    }

    // Default value.
    if let v = defaultValue {
      result.append(" = \(printer.show(v))")
    }

    return result
  }

}
