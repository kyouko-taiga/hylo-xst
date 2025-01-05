/// Properties about the representation of a type or term.
public struct ValueProperties: Hashable, OptionSet {

  /// The raw value of these properties.
  public let rawValue: UInt8

  /// Creates an instance from its raw value.
  public init(rawValue: UInt8) {
    self.rawValue = rawValue
  }

  /// Returns the union of `l` with `r`.
  public static func | (l: Self, r: Self) -> Self {
    l.union(r)
  }

  /// The value contains one or more errors.
  public static let hasError = ValueProperties(rawValue: 1 << 0)

  /// The value contains open variables.
  public static let hasVariable = ValueProperties(rawValue: 1 << 1)

  /// The value contains skolems (aka rigid variables).
  public static let hasSkolem = ValueProperties(rawValue: 1 << 2)

  /// The value contains type aliasess.
  public static let hasAliases = ValueProperties(rawValue: 1 << 3)

}
