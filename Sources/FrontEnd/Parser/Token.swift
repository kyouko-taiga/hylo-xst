import Archivist
import Utilities

/// A terminal symbol of the syntactic grammar.
public struct Token: Hashable {

  /// The kind of a token.
  public enum Kind: UInt8 {

    // Identifiers
    case name
    case underscore

    // Reserved keywords
    case `class`
    case `extension`
    case `false`
    case fun
    case `import`
    case infix
    case `inout`
    case `internal`
    case `let`
    case postfix
    case prefix
    case `private`
    case `public`
    case set
    case sink
    case trait
    case `true`
    case type

    // Operators
    case ampersand
    case arrow
    case assign
    case equal
    case `operator`

    // Punctuation
    case comma
    case dot
    case colon
    case doubleColon
    case semicolon

    // Delimiters
    case leftAngle
    case rightAngle
    case leftBrace
    case rightBrace
    case leftBracket
    case rightBracket
    case leftParenthesis
    case rightParenthesis

    // Errors
    case error
    case unterminatedBlockComment

  }

  /// The kind of the token.
  public let kind: Kind

  /// The site from which `self` was extracted.
  public let site: SourceSpan

  /// Creates an instance with the given properties.
  public init(kind: Kind, site: SourceSpan) {
    self.kind = kind
    self.site = site
  }

  /// The text of this token.
  public var text: Substring { site.text }

  /// `true` iff `self` is a reserved keyword.
  public var isKeyword: Bool {
    (kind.rawValue >= Kind.false.rawValue) && (kind.rawValue <= Kind.type.rawValue)
  }

  /// `true` iff `self` may be at the beginning of a declaration.
  public var isDeclarationHead: Bool {
    switch kind {
    case .fun, .import, .trait, .type:
      return true
    default:
      return isDeclarationModifier
    }
  }

  /// `true` iff `self` is a declaration modifier.
  public var isDeclarationModifier: Bool {
    switch kind {
    case .private, .public, .internal:
      return true
    default:
      return false
    }
  }

  /// `true` iff `self` is an operator notation.
  public var isOperatorNotation: Bool {
    switch kind {
    case .infix, .postfix, .prefix:
      return true
    default:
      return false
    }
  }

  /// `true` iff `self` may be part of an operator.
  public var isOperator: Bool {
    switch kind {
    case .ampersand, .equal, .operator, .leftAngle, .rightAngle:
      return true
    default:
      return false
    }
  }

  /// `true` iff `self` is a valid argument label.
  public var isArgumentLabel: Bool {
    (kind == .name) || (kind == .underscore) || isKeyword
  }

}

extension Token: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    let k = try archive.read(rawValueOf: Token.Kind.self, in: &context)
      .unwrapOrThrow(ArchiveError.invalidInput)
    let s = try archive.read(SourceSpan.self, in: &context)
    self.init(kind: k, site: s)
  }
  
  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(rawValueOf: kind, in: &context)
    try archive.write(site, in: &context)
  }

}
