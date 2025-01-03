/// A term or type computed at compile-time.
public enum Value: Hashable {

  /// A term.
  case term(AnyTerm)

  /// A type.
  case type(AnyTypeIdentity)

  /// Creates an instance equal to `t`.
  public init<T: Term>(_ t: T) {
    self = .term(.init(t))
  }

  /// Properties about `self`.
  public var properties: ValueProperties {
    switch self {
    case let .term(t): t.properties
    case let .type(t): t.properties
    }
  }

  /// Returns `self` if it a term of type `T`; otherwise, returns `nil`.
  public func cast<T: Term>(as: T.Type) -> T? {
    if case .term(let t) = self {
      return t.wrapped as? T
    } else {
      return nil
    }
  }

  /// The value of `self` as a type or `nil` if `self` is a term.
  public var type: AnyTypeIdentity? {
    if case .type(let t) = self { t } else { nil }
  }

}

