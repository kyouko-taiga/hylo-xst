import Archivist
import Utilities

/// The declaration of a function or subscript parameter.
public struct ParameterDeclaration: Declaration & Scope {

  /// The label of the parameter.
  public let label: Parsed<String>?

  /// The identifier of the parameter.
  public let identifier: Parsed<String>

  /// The type ascription of the parameter.
  public let ascription: ExpressionIdentity?

  /// The site from which `self` was parsed.
  public var site: SourceSpan

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    var result = ""

    // Label and identifier.
    if let l = label {
      result.append(l.value == identifier.value ? identifier.value :  "\(l.value) \(identifier.value)")
    } else {
      result.append("_ \(identifier.value)")
    }

    // Ascription.
    if let a = ascription {
      result.append(": \(program.show(a))")
    }

    return result
  }

}

extension ParameterDeclaration: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.label = try archive.read(Parsed<String>?.self, in: &context)
    self.identifier = try archive.read(Parsed<String>.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
    self.ascription = try archive.read(ExpressionIdentity?.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(label, in: &context)
    try archive.write(identifier, in: &context)
    try archive.write(site, in: &context)
    try archive.write(ascription, in: &context)
  }

}
