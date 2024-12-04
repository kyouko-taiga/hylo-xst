/// A type denoting the identity of type tree.
public protocol TypeIdentity: Hashable {

  /// The type-erased value of this identity.
  var erased: AnyTypeIdentity { get }

}

extension TypeIdentity {

  /// Properties of the identified type.
  public var properties: ValueProperties {
    erased.properties
  }

}

/// The type-erased identity of a type tree.
///
/// An identity is composed of a 8-bit option set representing some properties of the identified
/// type, together with a 56-bit payload representing a position in a type store.
public struct AnyTypeIdentity: Hashable {

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

  /// Creates an identifying the same node as `other`.
  public init<T: TypeIdentity>(_ other: T) {
    self.bits = other.erased.bits
  }

  /// The offset of the identified type in its store.
  public var offset: Int {
    .init(bits >> 8)
  }

  /// Properties of the identified type.
  public var properties: ValueProperties {
    .init(rawValue: .init(bits & 0xff))
  }

  /// Returns whether the specified flags are raised for `self`.
  public subscript(f: ValueProperties) -> Bool {
    properties.contains(f)
  }

  /// The identity of the error type.
  public static let error = AnyTypeIdentity(offset: 1 << 55, properties: .hasError)

  /// The identity of `Hylo.Void`, which is an empty tuple.
  public static let void = AnyTypeIdentity(offset: (1 << 55) | 0x01, properties: [])

  /// The identity of `Hylo.Never`, which is an empty union.
  public static let never = AnyTypeIdentity(offset: (1 << 55) | 0x02, properties: [])

}

/// A type denoting the identity of type tree.
extension AnyTypeIdentity: TypeIdentity {

  /// The type-erased value of this identity.
  public var erased: AnyTypeIdentity {
    self
  }

}

extension AnyTypeIdentity: ExpressibleByIntegerLiteral {

  public init(integerLiteral value: UInt64) {
    self.init(bits: value)
  }

}

extension AnyTypeIdentity: CustomStringConvertible {

  public var description: String { bits.description }

}

/// The identity of a type tree.
public struct ConcreteTypeIdentity<T: TypeTree>: TypeIdentity {

  /// The type-erased value of this identity.
  public let erased: AnyTypeIdentity

  /// Creates an instance with the given raw value.
  internal init(uncheckedFrom erased: AnyTypeIdentity) {
    self.erased = erased
  }

    /// Returns `true` iff `l` denotes the same tree as `r`.
    public static func == <U: TypeIdentity>(l: Self, r: U) -> Bool {
      l.erased == r.erased
    }
  
    /// Returns `true` iff `l` denotes the same node as `r`.
    public static func == <U: TypeIdentity>(l: U, r: Self) -> Bool {
      l.erased == r.erased
    }

}
