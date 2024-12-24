import Archivist

/// The declaration of a (possibly empty) set of bindings.
public struct BindingDeclaration: Declaration {

  /// A pattern introducing the declared bindings.
  public let pattern: BindingPattern.ID

  /// The initializer of the declaration, if any.
  public let initializer: ExpressionIdentity?

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    let s = program.show(pattern)
    if let i = initializer {
      return "\(s) = \(program.show(i))"
    } else {
      return s
    }
  }

}

extension BindingDeclaration: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.pattern = try archive.read(BindingPattern.ID.self, in: &context)
    self.initializer = try archive.read(ExpressionIdentity?.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(pattern, in: &context)
    try archive.write(initializer)
    try archive.write(site)
  }

}
