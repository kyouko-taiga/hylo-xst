import Archivist
import Utilities

/// The declaration of an initializer.
public struct InitializerDeclaration: Declaration, Scope {

  /// The introducer of an initializer declaration.
  public enum Introducer: UInt8 {

    /// The initializer introducer, `init`.
    case `init`

    /// The memberwise initializer introducer, `memberwise init`
    case memberwiseinit

  }

  /// The introducer of this declaration.
  public let introducer: Parsed<Introducer>

  /// The declarations of the initializer's parameters.
  public let parameters: [ParameterDeclaration.ID]

  /// The body of the function.
  public let body: [StatementIdentity]?

  /// The site from which `self` was parsed.
  public let site: SourceSpan

  /// `true` iff `self` denotes a memberwise initializer.
  public var isMemberwise: Bool {
    introducer.value == .memberwiseinit
  }

}

extension InitializerDeclaration: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    ""
  }

}

extension InitializerDeclaration: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    fatalError()
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    fatalError()
  }

}


extension InitializerDeclaration.Introducer: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self = try archive.read(rawValueOf: Self.self, in: &context)
      .unwrapOrThrow(ArchiveError.invalidInput)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(rawValueOf: self)
  }

}
