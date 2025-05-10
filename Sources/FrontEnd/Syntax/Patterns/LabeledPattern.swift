import Archivist

/// A pattern with an optional label.
@Archivable
public struct LabeledPattern: Hashable, Sendable {

  /// The label of the pattern, if any.
  public let label: Parsed<String>?

  /// The pattern.
  public let value: PatternIdentity

  /// Creates an instance with the given properties.
  public init(label: Parsed<String>?, value: PatternIdentity) {
    self.label = label
    self.value = value
  }

}

extension LabeledPattern: LabeledSyntax {

  public typealias Value = PatternIdentity

}

extension LabeledPattern: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let v = printer.show(value)
    return if let l = label { "\(l): \(v)" } else { v }
  }

}
