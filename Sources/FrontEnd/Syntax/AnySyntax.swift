import Archivist

/// A type-erasing container for nodes in an abstract syntax tree.
internal struct AnySyntax: Sendable {

  /// The node wrapped in this container.
  internal let wrapped: any Syntax

  /// Creates an instance wrapping `n`.
  internal init(_ n: any Syntax) {
    self.wrapped = n
  }

}

extension AnySyntax: Equatable {

  internal static func == (l: Self, r: Self) -> Bool {
    l.wrapped.equals(r.wrapped)
  }

}

extension AnySyntax: Archivable {

  internal init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    let k = try archive.read(SyntaxTag.self, in: &context)
    self = .init(try archive.read(k.value, in: &context))
  }

  internal func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(SyntaxTag(type(of: wrapped)), in: &context)
    try archive.write(wrapped, in: &context)
  }

}
