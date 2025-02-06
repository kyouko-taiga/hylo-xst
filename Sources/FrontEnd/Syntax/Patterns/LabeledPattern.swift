import Archivist

/// A pattern with an optional label.
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

extension LabeledPattern: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.label = try archive.read(Parsed<String>.self, in: &context)
    self.value = try archive.read(PatternIdentity.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(label, in: &context)
    try archive.write(value, in: &context)
  }

}
