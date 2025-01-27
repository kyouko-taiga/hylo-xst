import Archivist

/// The application of a function, method, or subscript.
public struct Call: Expression {

  /// The way in which an entity is being applied.
  public enum Style: UInt8, Hashable {

    /// Entity called with parentheses.
    case parenthesized

    /// Entity called with brackets.
    case bracketed

  }

  /// The function or method being applied.
  public let callee: ExpressionIdentity

  /// The arguments passed to the callee.
  public let arguments: [LabeledExpression]

  /// The way in which the arguments are passed.
  public let style: Style

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// Returns a copy of `self` with the callee replaced.
  public func replacing(callee: ExpressionIdentity) -> Call {
    .init(callee: callee, arguments: arguments, style: style, site: site)
  }

  /// Returns a copy of `self` with the arguments replaced.
  public func replacing(arguments: [LabeledExpression]) -> Call {
    .init(callee: callee, arguments: arguments, style: style, site: site)
  }

  /// The labels of the arguments.
  public var labels: [String?] {
    arguments.map(\.label?.value)
  }

}

extension Call: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    let c = printer.show(callee)
    let a = arguments.map({ (a) in printer.show(a) }).joined(separator: ", ")
    switch style {
    case .parenthesized:
      return "\(c)(\(a))"
    case .bracketed:
      return "\(c)[\(a)]"
    }
  }

}

extension Call: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.callee = try archive.read(ExpressionIdentity.self, in: &context)
    self.arguments = try archive.read([LabeledExpression].self, in: &context)
    self.style = try archive.read(Style.self, in: &context)
    self.site = try archive.read(SourceSpan.self, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(callee, in: &context)
    try archive.write(arguments, in: &context)
    try archive.write(style, in: &context)
    try archive.write(site, in: &context)
  }

}

extension Call.Style: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self = try archive.read(rawValueOf: Self.self, in: &context)
      .unwrapOrThrow(ArchiveError.invalidInput)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(rawValueOf: self)
  }

}
