/// A term computed at compile-time.
public protocol Term: Hashable {

  /// The type of the term.
  var type: AnyTypeIdentity { get }

  /// Properties of the term.
  var properties: ValueProperties { get }

  /// Returns a parsable representation of `self`, which is a value in `program`.
  func show(readingChildrenFrom program: Program) -> String

}

extension Term {

  /// Returns `true` iff `self` is equal to `other`.
  public func equals(_ other: any Term) -> Bool {
    self == other as? Self
  }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    let t = program.show(type)
    return "<instance of \(t)>"
  }

}
