import Archivist

/// A type denoting a typing error.
public struct ErrorType: TypeTree {

  /// Creates an instance.
  public init() {}

  /// Properties about `self`.
  public var properties: ValueProperties {
    .hasError
  }

}

extension ErrorType: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "#!"
  }

}

extension ErrorType: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    fatalError()
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    fatalError()
  }

}
