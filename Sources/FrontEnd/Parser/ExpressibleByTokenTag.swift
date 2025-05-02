/// A type whose instances can be created from a single token.
internal protocol ExpressibleByTokenTag {

  /// Creates an instance from `tag`.
  init?(tag: Token.Tag)

}
