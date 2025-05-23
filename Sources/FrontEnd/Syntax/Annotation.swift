import Archivist

/// An annotation on a syntax tree.
@Archivable
public struct Annotation: Hashable, Sendable {

  /// The name of the annotation.
  public let identifier: Parsed<String>

  /// The arguments of the annotation.
  public let arguments: [LabeledExpression]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(identifier: Parsed<String>, arguments: [LabeledExpression], site: SourceSpan) {
    self.identifier = identifier
    self.arguments = arguments
    self.site = site
  }

}

extension Annotation: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    if arguments.isEmpty {
      return "@\(identifier.value)"
    } else {
      let a = arguments.map({ (a) in printer.show(a) }).joined(separator: ", ")
      return "@\(identifier.value)(\(a))"
    }
  }

}
