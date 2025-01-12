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
/// type, together with a 56-bit payload representing either a position in a type store or the
/// value of the identified type tree.
///
/// The properties are stored in the 8 least significant bits. The two highest bits of the payload
/// act as a discriminator where:
/// - `0b10` denotes a predefined type; and
/// - `0b11` denotes a type variable.
public struct AnyTypeIdentity: Hashable {

  /// The bit representation of `self`.
  public let bits: UInt64

  /// Creates an instance with the given bit representation.
  public init(bits: UInt64) {
    self.bits = bits
  }

  /// Creates an instance identifying the same node as `other`.
  public init<T: TypeIdentity>(_ other: T) {
    self.bits = other.erased.bits
  }

  /// Creates an instance identifying a tree at offset `n`, having properties `ps`.
  public init(offset n: Int, properties ps: ValueProperties) {
    assert(n >> 56 == 0)
    self.bits = (UInt64(ps.rawValue) << 56) | UInt64(n)
  }

  /// Creates an instance identifying a type variable with the given identifier.
  public init(variable n: Int) {
    assert(n >> 54 == 0)
    self.bits = (UInt64(ValueProperties.hasVariable.rawValue) << 56) | (0b11 << 54) | UInt64(n)
  }

  /// Creates an instance identifying the predifined type `n`, having properties `ps`.
  private init(predefined n: UInt64, properties ps: ValueProperties) {
    assert(n >> 54 == 0)
    self.bits = (UInt64(ps.rawValue) << 56) | (0b10 << 54) | n
  }

  /// The offset of the identified type in its store.
  public var offset: Int {
    .init(bits & ~(0xff << 56))
  }

  /// Properties of the identified type.
  public var properties: ValueProperties {
    .init(rawValue: .init(bits >> 56))
  }

  /// `true` iff `self` is the identity of `Hylo.Void` or `Hylo.Never`.
  public var isVoidOrNever: Bool {
    self == .void || self == .never
  }

  /// `true` iff `self` is a type variable.
  public var isVariable: Bool {
    let m = UInt64(0b11) << 54
    return self.bits & m == m
  }

  /// Returns `self` iff it is not `.error`. Otherwise, returns `nil`.
  public var unlessError: AnyTypeIdentity? {
    self == .error ? nil : self
  }

  /// Returns whether the specified flags are raised for `self`.
  public subscript(f: ValueProperties) -> Bool {
    properties.contains(f)
  }

  /// The identity of the error type.
  public static let error = AnyTypeIdentity(predefined: 0, properties: .hasError)

  /// The identity of `Hylo.Void`, which is an empty tuple.
  public static let void = AnyTypeIdentity(predefined: 1, properties: [])

  /// The identity of `Hylo.Never`, which is an empty union.
  public static let never = AnyTypeIdentity(predefined: 2, properties: [])

}

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
