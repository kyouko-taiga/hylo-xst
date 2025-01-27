import Archivist

/// A clause describing contextual parameters and contextual constraints taken at compile-time.
public struct StaticParameters: Equatable {

  /// The explicit parameters of the list.
  public let explicit: [GenericParameterDeclaration.ID]

  /// The constraints in the clause.
  public let implicit: [DeclarationIdentity]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// `true` iff `self` doesn't contain any parameter or constraint.
  public var isEmpty: Bool {
    explicit.isEmpty && implicit.isEmpty
  }

  /// Returns an empty clause anchored at `site`.
  public static func empty(at site: SourceSpan) -> StaticParameters {
    .init(explicit: [], implicit: [], site: site)
  }

}

extension StaticParameters: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    if implicit.isEmpty {
      return "<\(printer.show(explicit))>"
    } else {
      return "<\(printer.show(explicit)) where \(printer.show(implicit))>"
    }
  }

}


extension StaticParameters: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.explicit = try archive.read([GenericParameterDeclaration.ID].self, in: &context)
    self.implicit = try archive.read([DeclarationIdentity].self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(explicit, in: &context)
    try archive.write(implicit, in: &context)
    try archive.write(site, in: &context)
  }

}
