import Archivist

/// A pattern that matches tuples.
public struct TuplePattern: Pattern {

  /// The elements of the pattern.
  public let elements: [LabeledPattern]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

}

extension TuplePattern: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    if elements.count == 1 {
      return "(\(printer.show(elements)),)"
    } else {
      return "(\(printer.show(elements)))"
    }
  }

}

extension TuplePattern: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.elements = try archive.read([LabeledPattern].self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(elements, in: &context)
    try archive.write(site, in: &context)
  }

}
