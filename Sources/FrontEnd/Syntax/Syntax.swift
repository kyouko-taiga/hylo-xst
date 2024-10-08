import Archivist

/// A node in an abstract syntax tree.
public protocol Syntax: Equatable, Archivable {

  /// The site from which `self` was parsed.
  var site: SourceSpan { get }

  /// Returns a parsable representation of `self`, which is a node of `program`.
  func show(readingChildrenFrom program: Program) -> String

}

extension Syntax {

  /// The identity of an instance of `Self`.
  public typealias ID = ConcreteSyntaxIdentity<Self>

  /// Returns `true` iff `self` is equal to `other`.
  public func equals(_ other: any Syntax) -> Bool {
    self == other as? Self
  }

}
