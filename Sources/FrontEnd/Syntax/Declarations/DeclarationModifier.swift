import Archivist

/// A modifier on a declaration.
public enum DeclarationModifier: UInt8, Sendable {

  /// The modifier for introducing members stored out-of-line.
  case indirect

  /// The modifier for introducing a static member.
  case `static`

  /// The modifier for introducing a private entity.
  case `private`

  /// The modifier for introducing an entity public up to the module boundary.
  case `internal`

  /// The modifier for introducing a public entity.
  case `public`

  /// Returns `true` iff `self` can appear after `other` in sources.
  public func canOccurAfter(_ other: DeclarationModifier) -> Bool {
    switch self {
    case .indirect, .static:
      return true
    default:
      assert(isAccessModifier)
      return false
    }
  }

  /// Returns `true` iff `self` and `other` can be applied on the same declaration.
  public func canOccurWith(_ other: DeclarationModifier) -> Bool {
    switch self {
    case .indirect:
      return (other != self) && (other != .static)
    case .static:
      return (other != self) && (other != .indirect)
    default:
      assert(isAccessModifier)
      return !other.isAccessModifier
    }
  }

  /// Returns `true` iff `self` is an access modifier.
  public var isAccessModifier: Bool {
    switch self {
    case .private, .internal, .public:
      return true
    default:
      return false
    }
  }

  /// Returns `true` iff `self` can be applied to a conformance declaration.
  public var isApplicableToConformance: Bool {
    isAccessModifier
  }

  /// Returns `true` iff `self` can be applied on an initializer declaration.
  public var isApplicableToInitializer: Bool {
    isAccessModifier
  }

  /// Returns `true` iff `self` can be applied on a type declaration.
  public var isApplicableToTypeDeclaration: Bool {
    isAccessModifier
  }

}

extension DeclarationModifier: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self = try archive.read(rawValueOf: Self.self, in: &context)
      .unwrapOrThrow(ArchiveError.invalidInput)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(rawValueOf: self)
  }

}
