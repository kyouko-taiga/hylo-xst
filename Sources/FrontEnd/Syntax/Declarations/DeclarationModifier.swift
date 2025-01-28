import Archivist

/// A member or access modifier on a declaration.
public enum DeclarationModifier: UInt8 {

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
    case .static:
      return true
    default:
      return other != .static
    }
  }

  /// Returns `true` iff `self` and `other` can be applied on the same declaration.
  public func canOccurWith(_ other: DeclarationModifier) -> Bool {
    if self == .static {
      return other != .static
    } else {
      return other == .static
    }
  }

  /// Returns `true` iff `self` can be applied on an initializer declaration.
  public var isApplicableToInitializer: Bool {
    self != .static
  }

  /// Returns `true` iff `self` can be applied on a type declaration.
  public var isApplicableToTypeDeclaration: Bool {
    self != .static
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
