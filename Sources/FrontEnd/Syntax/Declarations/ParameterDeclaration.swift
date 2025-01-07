import Archivist

/// The declaration of a function or subscript parameter.
public struct ParameterDeclaration: Declaration {

  /// The label of the parameter.
  public let label: Parsed<String>?

  /// The identifier of the parameter.
  public let identifier: Parsed<String>

  /// The type ascription of the parameter, if any.
  public let ascription: RemoteTypeExpression.ID?

  /// The default value of the parameter, if any.
  public let `default`: ExpressionIdentity?

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    var result = ""

    // Label and identifier.
    switch label {
    case .some(let l) where l.value == identifier.value:
      result.append(identifier.value)
    case .some(let l):
      result.append("\(l) \(identifier)")
    case nil:
      result.append("_ \(identifier)")
    }

    // Ascription.
    if let a = ascription {
      result.append(": \(program.show(a))")
    }

    // Default value.
    if let v = `default` {
      result.append(" = \(program.show(v))")
    }

    return result
  }

}

extension ParameterDeclaration: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.label = try archive.read(Parsed<String>?.self, in: &context)
    self.identifier = try archive.read(Parsed<String>.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
    self.ascription = try archive.read(RemoteTypeExpression.ID?.self, in: &context)
    self.default = try archive.read(ExpressionIdentity?.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(label, in: &context)
    try archive.write(identifier, in: &context)
    try archive.write(site, in: &context)
    try archive.write(ascription, in: &context)
    try archive.write(`default`, in: &context)
  }

}
