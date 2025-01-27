import Archivist

/// A node in an abstract syntax tree.
public protocol Syntax: Equatable, Archivable, Showable {

  /// The site from which `self` was parsed.
  var site: SourceSpan { get }

}

extension Syntax {

  /// The identity of an instance of `Self`.
  public typealias ID = ConcreteSyntaxIdentity<Self>

  /// Returns `true` iff `self` is equal to `other`.
  public func equals(_ other: any Syntax) -> Bool {
    self == other as? Self
  }

}
