/// The raw value of a type tree identity.
///
/// A raw identity is composed of a 8-bit option set representing some properties of the identified
/// type, together with a 56-bit payload representing a position in a type store.
public struct RawTypeIdentity: Hashable {

  /// The bit representation of `self`.
  public let bits: UInt64

  /// Creates an instance with the given bit representation.
  public init(bits: UInt64) {
    self.bits = bits
  }

  /// Creates an instance identifying a tree at offset `n`, having properties `ps`.
  public init(offset n: Int, properties ps: ValueProperties) {
    assert(n >> 56 == 0)
    assert(UInt64(ps.rawValue) & ~0xff == 0)
    self.bits = UInt64(bitPattern: Int64(n << 8)) | UInt64(ps.rawValue)
  }

  /// The offset of the identified type in its store.
  public var offset: Int {
    .init(bits >> 8)
  }

  /// Properties of the identified type.
  public var properties: ValueProperties {
    .init(rawValue: .init(bits & 0xff))
  }

}

extension RawTypeIdentity: ExpressibleByIntegerLiteral {

  public init(integerLiteral value: UInt64) {
    self.init(bits: value)
  }

}

extension RawTypeIdentity: CustomStringConvertible {

  public var description: String { bits.description }

}

/// A type denoting the identity of type tree.
public protocol TypeIdentity: Hashable {

  /// The raw value of this identity.
  var rawValue: RawTypeIdentity { get }

}

extension TypeIdentity {

  /// Properties of the identified type.
  public var properties: ValueProperties {
    rawValue.properties
  }

  /// Returns `true` iff `l` denotes the same tree as `r`.
  public static func == <T: TypeIdentity>(l: Self, r: T) -> Bool {
    l.rawValue == r.rawValue
  }

  /// Returns `true` iff `l` denotes the same node as `r`.
  public static func == <T: TypeIdentity>(l: T, r: Self) -> Bool {
    l.rawValue == r.rawValue
  }

}

/// The identity of a type tree.
public struct ConcreteTypeIdentity<T: TypeTree>: TypeIdentity {

  /// The raw value of this identity.
  public let rawValue: RawTypeIdentity

  /// Creates an instance with the given raw value.
  public init(rawValue: RawTypeIdentity) {
    self.rawValue = rawValue
  }

  /// Returns a type-erased copy of `t`.
  public postfix static func ^ (t: Self) -> AnyTypeIdentity {
    .init(t)
  }

}

/// The type-erased identity of a type tree.
public struct AnyTypeIdentity: TypeIdentity {

  /// The raw value of this identity.
  public let rawValue: RawTypeIdentity

  /// Creates an instance with the given raw value.
  public init(rawValue: RawTypeIdentity) {
    self.rawValue = rawValue
  }

  /// Creates an instance equal to `other`.
  public init<T: TypeIdentity>(_ other: T) {
    self.rawValue = other.rawValue
  }

  /// Returns whether the specified flags are raised for `self`.
  public subscript(f: ValueProperties) -> Bool {
    properties.contains(f)
  }

  /// The identity of the error type.
  public static let error = AnyTypeIdentity(
    rawValue: .init(offset: 1 << 55, properties: .hasError))

  /// The identity of `Hylo.Void`, which is an empty tuple.
  public static let void = AnyTypeIdentity(
    rawValue: .init(offset: (1 << 55) | 0x01, properties: []))

  /// The identity of `Hylo.Never`, which is an empty union.
  public static let never = AnyTypeIdentity(
    rawValue: .init(offset: (1 << 55) | 0x02, properties: []))

}
