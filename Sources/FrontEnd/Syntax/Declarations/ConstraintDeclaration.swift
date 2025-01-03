import Archivist

///// The declaration of a conformance constraint in a context clause.
//public struct ConformanceConstraint: Declaration {
//
//  /// The type for which the conformance is declared.
//  public let extendee: ExpressionIdentity
//
//  /// The trait to which the conformance is declared.
//  public let concept: ExpressionIdentity
//
//  /// The site from which `self` was parsed.
//  public let site: SourceSpan
//
//  /// Returns a parsable representation of `self`, which is a node of `program`.
//  public func show(readingChildrenFrom program: Program) -> String {
//    "\(program.show(extendee)): \(program.show(concept))"
//  }
//
//}
//
//extension ConformanceConstraint: Archivable {
//
//  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
//    self.extendee = try archive.read(ExpressionIdentity.self, in: &context)
//    self.concept = try archive.read(ExpressionIdentity.self, in: &context)
//    self.site = try archive.read(SourceSpan.self, in: &context)
//  }
//
//  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
//    try archive.write(extendee, in: &context)
//    try archive.write(concept, in: &context)
//    try archive.write(site, in: &context)
//  }
//
//}

/// The declaration of a constraint in a context clause.
public enum ConstraintDeclaration: Equatable {

  /// A parameter accepting a witness `extendee`' conformance to `concept`.
  case conformance(extendee: ExpressionIdentity, concept: ExpressionIdentity)

}

extension ConstraintDeclaration: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    switch try archive.readByte() {
    case 0:
      let t = try archive.read(ExpressionIdentity.self, in: &context)
      let u = try archive.read(ExpressionIdentity.self, in: &context)
      self = .conformance(extendee: t, concept: u)
    default:
      throw ArchiveError.invalidInput
    }
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    switch self {
    case .conformance(let t, let u):
      archive.write(byte: 0)
      try archive.write(t, in: &context)
      try archive.write(u, in: &context)
    }
  }

}

extension Program {

  /// Returns a source-like representation of `d`.
  public func show(_ d: ConstraintDeclaration) -> String {
    switch d {
    case .conformance(let t, let u):
      return "\(show(t)): \(show(u))"
    }
  }

}
