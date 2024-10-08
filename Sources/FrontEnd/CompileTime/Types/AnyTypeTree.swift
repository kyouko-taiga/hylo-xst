/// A type-erasing container for type trees.
internal struct AnyTypeTree {

  /// The node wrapped in this container.
  internal let wrapped: any TypeTree

  /// Creates an instance wrapping `n`.
  internal init(_ n: any TypeTree) {
    self.wrapped = n
  }

}

extension AnyTypeTree: Equatable {

  internal static func == (l: Self, r: Self) -> Bool {
    l.wrapped.equals(r.wrapped)
  }

}

extension AnyTypeTree: Hashable {

  internal func hash(into hasher: inout Hasher) {
    wrapped.hash(into: &hasher)
  }

}
