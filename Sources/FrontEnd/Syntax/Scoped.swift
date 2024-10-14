/// A pair composed of a value and a scope.
public struct Scoped<T> {

  /// The value.
  public let value: T

  /// The scope.
  public let scope: ScopeIdentity

  /// Creates an instance pairing `value` with `scope`.
  public init(_ value: T, in scope: ScopeIdentity) {
    self.value = value
    self.scope = scope
  }

}

extension Scoped: Equatable where T: Equatable {}

extension Scoped: Hashable where T: Hashable {}
