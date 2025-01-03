/// The static context of a generic declaration.
public struct StaticContext: Equatable {

  /// Conformances given in the context.
  public private(set) var givens: [Model]

  /// Creates an empty context.
  internal init() {
    self.givens = []
  }

  /// Adds `m` to this context.
  internal mutating func add(_ m: Model) {
    self.givens.append(m)
  }

}
