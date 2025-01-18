/// A term denoting an compile-time evaluation error.
public struct ErrorTerm: Term {

  /// The type of the term.
  public var type: AnyTypeIdentity {
    .error
  }

  /// Properties about `self`.
  public var properties: ValueProperties {
    .hasError
  }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    "$!"
  }

}
