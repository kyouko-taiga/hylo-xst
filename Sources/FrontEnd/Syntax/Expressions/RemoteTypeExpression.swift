import Archivist
import Utilities

/// The expression of a remote type.
public struct RemoteTypeExpression: Expression {

  /// The capabilities of the projection.
  public let access: Parsed<AccessEffect>

  /// The type of the projected value.
  public let projectee: ExpressionIdentity

  /// The site from which `self` was parsed.
  public let site: SourceSpan

}

extension RemoteTypeExpression: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "\(access) \(printer.show(projectee))"
  }

}

extension RemoteTypeExpression: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    fatalError()
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    fatalError()
  }

}
