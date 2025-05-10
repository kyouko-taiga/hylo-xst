import Archivist

/// The expression of an arrow type.
@Archivable
public struct ArrowExpression: Expression {

  /// A parameter in the expression of an arrow type.
  @Archivable
  public struct Parameter: Hashable, Sendable {

    /// The label of the parameter.
    public let label: Parsed<String>?

    /// The type ascription of the parameter.
    public let ascription: RemoteTypeExpression.ID

    /// Creates an instance with the given values.
    public init(label: Parsed<String>?, ascription: RemoteTypeExpression.ID) {
      self.label = label
      self.ascription = ascription
    }

  }

  /// The environment of the lambda, or `nil` if the environment is `[]`.
  public let environment: ExpressionIdentity?

  /// The parameters of the lambda.
  public let parameters: [Parameter]

  /// The effect of the function's call operator.
  public let effect: Parsed<AccessEffect>

  /// The type of the function's return value.
  public let output: ExpressionIdentity

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  public init(
    environment: ExpressionIdentity?,
    parameters: [Parameter],
    effect: Parsed<AccessEffect>,
    output: ExpressionIdentity,
    site: SourceSpan
  ) {
    self.environment = environment
    self.parameters = parameters
    self.effect = effect
    self.output = output
    self.site = site
  }

}

extension ArrowExpression: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    var result = ""

    if let e = environment {
      result.append("[\(printer.show(e))]")
    } else {
      result.append("[]")
    }

    result.append("(")
    result.append(printer.show(parameters))
    result.append(") \(effect.value) -> ")
    result.append(printer.show(output))

    return result
  }

}

extension ArrowExpression.Parameter: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    if let l = label {
      return "\(l): \(printer.show(ascription))"
    } else {
      return printer.show(ascription)
    }
  }

}
