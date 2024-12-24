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

  /// Returns a parsable representation of `self`, which is a node of `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    "\(access) \(program.show(projectee))"
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
