import Archivist

/// The implicit qualification of a name expression, e.g., the `.` in `.bar`.
public struct ImplicitQualification: Expression {

  /// The site from which `self` was parsed.
  public let site: SourceSpan

}


extension ImplicitQualification: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "."
  }

}

extension ImplicitQualification: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(site, in: &context)
  }

}
