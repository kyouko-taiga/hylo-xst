/// A diagnostic related to a region of Hylo source code.
public struct Diagnostic: Hashable {

  /// The severity of a diagnostic.
  public enum Level: Hashable, Comparable {

    /// A note.
    case note

    /// An error that does not prevent compilation.
    case warning

    /// An unrecoverable error that prevents compilation.
    case error

  }

  /// The level of the diagnostic.
  public let level: Level

  /// The main description of the diagnostic.
  ///
  /// The message should be general and able to stand on its own.
  public let message: String

  /// The source code or source position (if empty) identified as the cause of the error.
  public let site: SourceSpan

  /// The sub-diagnostics.
  public let notes: [Diagnostic]

  /// Creates a new diagnostic.
  ///
  /// - Requires: elements of `notes` have `self.level == .note`
  public init(
    _ level: Level, _ message: String, at site: SourceSpan, notes: [Diagnostic] = []
  ) {
    precondition(notes.allSatisfy({ $0.level == .note }))
    self.level = level
    self.message = message
    self.site = site
    self.notes = notes
  }

}

extension Diagnostic: Comparable {

  public static func < (l: Self, r: Self) -> Bool {
    let s = l.site
    let t = r.site

    if s.source != t.source {
      return s.source.name.lexicographicallyPrecedes(t.source.name)
    } else if s.start != t.start {
      return s.start < t.start
    } else if l.level != r.level {
      return l.level > r.level
    } else if l.message != r.message {
      return l.message.lexicographicallyPrecedes(r.message)
    } else {
      return l.notes.lexicographicallyPrecedes(r.notes)
    }
  }

}

extension Diagnostic: CustomStringConvertible {

  public var description: String {
    "\(site.gnuStandardText()): \(level): \(message)"
  }

}

extension Program {

  /// Returns an error diagnosing an illegal function application.
  internal func cannotCall(
    _ f: AnyTypeIdentity, _ s: Call.Style, at site: SourceSpan
  ) -> Diagnostic {
    switch s {
    case .parenthesized:
      let m = format("cannot call value of type '%T' as a function", [f])
      return .init(.error, m, at: site)
    case .bracketed:
      let m = format("cannot call value of type '%T' as a subscript", [f])
      return .init(.error, m, at: site)
    }
  }

  /// Returns an error diagnosing a duplicate declaration.
  internal func duplicateDeclaration(
    at site: SourceSpan, previousDeclarations: [SourceSpan] = []
  ) -> Diagnostic {
    let notes = previousDeclarations.map { (s) in
      Diagnostic(.note, "previous declaration here", at: s)
    }
    return .init(.error, "duplicate declaration", at: site, notes: notes)
  }

  /// Returns an error diagnosing incompatible labels in a function or subscript application.
  internal func incompatibleLabels<S1: Sequence<String?>, S2: Sequence<String?>>(
    found: S1, expected: S2, at site: SourceSpan
  ) -> Diagnostic {
    let m = """
      incompatible labels: found '(\(ArgumentLabels(found)))', \
      expected '(\(ArgumentLabels(expected)))'
      """
    return .init(.error, m, at: site)
  }

  /// Returns an error diagnosing name.
  internal func undefinedSymbol(_ n: Name, at site: SourceSpan) -> Diagnostic {
    .init(.error, "undefined symbol '\(n)'", at: site)
  }

}
