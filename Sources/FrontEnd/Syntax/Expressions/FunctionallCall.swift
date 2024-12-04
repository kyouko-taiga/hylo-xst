import Archivist

/// The application of a function or method.
public struct FunctionallCall: Expression {

  /// The function or method being applied.
  public let callee: ExpressionIdentity

  /// The arguments passed to the callee.
  public let arguments: [LabeledArgument]

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    let c = program.show(callee)
    let a = arguments.map(program.show(_:)).joined(separator: ", ")
    return "\(c)(\(a))"
  }

}

extension FunctionallCall: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.callee = try archive.read(ExpressionIdentity.self, in: &context)
    self.arguments = try archive.read([LabeledArgument].self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(callee, in: &context)
    try archive.write(arguments, in: &context)
    try archive.write(site, in: &context)
  }

}
