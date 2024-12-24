import Archivist

/// A pattern introducing a (possibly empty) set of bindings.
public struct BindingPattern: Pattern {

  /// The introducer of a binding pattern.
  public enum Introducer: UInt8 {

    case `let`, `var`, `inout`, sinklet

  }

  /// The introducer of this declaration.
  public let introducer: Parsed<Introducer>

  /// A tree containing the declarations of the bindings being introduced.
  public let pattern: PatternIdentity

  /// The type ascription of the parameter.
  public let ascription: ExpressionIdentity?

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    let s = "\(introducer) \(program.show(pattern))"
    if let a = ascription {
      return "\(s): \(program.show(a))"
    } else {
      return s
    }
  }

}

extension BindingPattern: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.introducer = try archive.read(Parsed<Introducer>.self, in: &context)
    self.pattern = try archive.read(PatternIdentity.self, in: &context)
    self.ascription = try archive.read(ExpressionIdentity?.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(introducer)
    try archive.write(pattern, in: &context)
    try archive.write(ascription, in: &context)
    try archive.write(site, in: &context)
  }

}

extension BindingPattern.Introducer: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self = try archive.read(rawValueOf: Self.self, in: &context)
      .unwrapOrThrow(ArchiveError.invalidInput)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(rawValueOf: self)
  }

}

extension BindingPattern.Introducer: CustomStringConvertible {

  public var description: String {
    switch self {
    case .let:
      return "let"
    case .var:
      return "var"
    case .inout:
      return "inout"
    case .sinklet:
      return "sink let"
    }
  }

}
