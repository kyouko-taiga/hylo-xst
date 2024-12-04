/// A type-erasing container for a term.
public struct AnyTerm {

  /// The term wrapped in this container.
  public let wrapped: any Term

  /// Creates an instance wrapping `t`.
  public init<T: Term>(_ t: T) {
    self.wrapped = t
  }

  /// Properties of the wrapped term.
  public var properties: ValueProperties {
    wrapped.properties
  }

  /// The error term.
  public static let error = AnyTerm(ErrorTerm())

}

extension AnyTerm: Equatable {

  public static func == (l: Self, r: Self) -> Bool {
    l.wrapped.equals(r.wrapped)
  }

}

extension AnyTerm: Hashable {

  public func hash(into hasher: inout Hasher) {
    wrapped.hash(into: &hasher)
  }

}
