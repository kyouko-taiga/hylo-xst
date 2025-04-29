/// The tokens of a source file.
public struct Lexer: IteratorProtocol, Sequence {

  /// A snapshot of a lexer's internal state.
  public typealias Backup = SourceFile.Index

  /// The source file being tokenized.
  public let source: SourceFile

  /// The current position of the lexer in `source`.
  public private(set) var position: SourceFile.Index

  /// Creates an instance enumerating the tokens in `source`.
  public init(tokenizing source: SourceFile) {
    self.source = source
    self.position = source.startIndex
  }

  /// Advances to the next token and returns it, or returns `nil` if no next token exists.
  public mutating func next() -> Token? {
    if let unterminated = discardWhitespacesAndComments() { return unterminated }
    guard let head = peek() else { return nil }

    if head.isIdentifierHead {
      return takeKeywordOrIdentifier()
    } else if head == "#" {
      return takePoundKeywordOrLiteral()
    } else if head.isOperator {
      return takeOperator()
    } else {
      return takePunctuationOrDelimiter()
    }
  }

  /// Returns a snapshot of `self`'s internal state that can be restored using `restore(_:)`.
  public func save() -> Backup {
    position
  }

  /// Restores the state of `self` from a snapshot.
  public mutating func restore(_ snapshot: Backup) {
    position = snapshot
  }

  /// Consumes and returns a keyword or identifier.
  private mutating func takeKeywordOrIdentifier() -> Token {
    let word = take(while: \.isIdentifierTail)

    if word == "as" {
      _ = take("!") ?? take("*")
      return .init(tag: .conversion, site: span(word.startIndex ..< position))
    }

    let tag: Token.Tag
    switch word {
    case "_": tag = .underscore
    case "auto": tag = .auto
    case "extension": tag = .extension
    case "false": tag = .false
    case "fun": tag = .fun
    case "given": tag = .given
    case "import": tag = .import
    case "infix": tag = .infix
    case "init": tag = .`init`
    case "inout": tag = .inout
    case "internal": tag = .internal
    case "let": tag = .let
    case "postfix": tag = .postfix
    case "prefix": tag = .prefix
    case "private": tag = .private
    case "public": tag = .public
    case "return": tag = .return
    case "set": tag = .set
    case "sink": tag = .sink
    case "static": tag = .static
    case "struct": tag = .struct
    case "subscript": tag = .subscript
    case "trait": tag = .trait
    case "true": tag = .true
    case "type": tag = .type
    case "typealias": tag = .typealias
    case "var": tag = .var
    case "where": tag = .where
    default: tag = .name
    }

    assert(!word.isEmpty)
    return .init(tag: tag, site: span(word.startIndex ..< word.endIndex))
  }

  /// Consumes and returns a keyword prefixed by a '#' symbol.
  private mutating func takePoundKeywordOrLiteral() -> Token {
    let start = position
    _ = take()

    let tag: Token.Tag
    switch take(while: \.isIdentifierTail) {
    case "": tag = .error
    default: tag = .poundLiteral
    }

    return .init(tag: tag, site: span(start ..< position))
  }

  /// Consumes and returns an operator.
  private mutating func takeOperator() -> Token {
    let start = position

    // Leading angle brackets are tokenized individually, to parse generic clauses.
    if peek()!.isAngleBracket {
      return takePunctuationOrDelimiter()
    }

    // Stars are tokenized individually, to parse kinds.
    if take("*") != nil {
      return .init(tag: .star, site: span(start ..< position))
    }

    let text = take(while: \.isOperator)
    let tag: Token.Tag
    switch text {
    case "&": tag = .ampersand
    case "=": tag = .assign
    case "->": tag = .arrow
    case "==": tag = .equal
    default: tag = .operator
    }
    return .init(tag: tag, site: span(start ..< position))
  }

  /// Consumes and returns a punctuation token if the input starts with a punctuation symbol;
  /// otherwise consumes a single character and returns an error token.
  private mutating func takePunctuationOrDelimiter() -> Token {
    let start = position
    let tag: Token.Tag
    switch take() {
    case "<": tag = .leftAngle
    case ">": tag = .rightAngle
    case "{": tag = .leftBrace
    case "}": tag = .rightBrace
    case "[": tag = .leftBracket
    case "]": tag = .rightBracket
    case "(": tag = .leftParenthesis
    case ")": tag = .rightParenthesis
    case ",": tag = .comma
    case ".": tag = .dot
    case ";": tag = .semicolon
    case ":": tag = take(":") == nil ? .colon : .doubleColon
    default: tag = .error
    }
    return .init(tag: tag, site: span(start ..< position))
  }

  /// Consumes and returns the next character.
  private mutating func take() -> Character {
    defer { position = source.index(after: position) }
    return source[position]
  }

  /// Returns the next character without consuming it or `nil` if all the input has been consumed.
  private func peek() -> Character? {
    position != source.endIndex ? source[position] : nil
  }

  /// Discards all whitespaces and comments preceding the next token, returning an error token iff
  /// the scanner encounters an unmatched block comment opening sequence.
  private mutating func discardWhitespacesAndComments() -> Token? {
    while position != source.endIndex {
      if source[position].isWhitespace {
        discard()
      } else if take("//") != nil {
        discard(while: { !$0.isNewline })
      } else if take("/*") != nil {
        var openedBlocks = 1
        let start = position
        while true {
          if take("/*") != nil {
            openedBlocks += 1
          } else if openedBlocks == 0 {
            break
          } else if take("*/") != nil {
            openedBlocks -= 1
          } else if position == source.endIndex {
            return .init(tag: .unterminatedBlockComment, site: span(start ..< position))
          } else {
            discard()
          }
        }
      } else {
        break
      }
    }
    return nil
  }

  /// Discards `count` characters.
  private mutating func discard(_ count: Int = 1) {
    position = source.index(position, offsetBy: count)
  }

  /// Discards characters until `predicate` isn't satisfied or all the input has been consumed.
  private mutating func discard(while predicate: (Character) -> Bool) {
    _ = take(while: predicate)
  }

  /// Returns the longest prefix of the input whose characters all satisfy `predicate` and advances
  /// the position of `self` until after that prefix.
  private mutating func take(while predicate: (Character) -> Bool) -> Substring {
    let start = position
    while (position != source.endIndex) && predicate(source[position]) {
      position = source.index(after: position)
    }
    return source.text[start ..< position]
  }

  /// If the input starts with `prefix`, returns the current position and advances to the position
  /// until after `prefix`. Otherwise, returns `nil`.
  private mutating func take(_ prefix: String) -> String.Index? {
    var newPosition = position
    for c in prefix {
      if newPosition == source.endIndex || source[newPosition] != c { return nil }
      newPosition = source.index(after: newPosition)
    }
    defer { position = newPosition }
    return position
  }

  /// Returns a source span covering `range`.
  private func span(_ range: Range<String.Index>) -> SourceSpan {
    .init(range, in: source)
  }

}

extension Character {

  /// `true` iff `self` is a letter or the underscore.
  fileprivate var isIdentifierHead: Bool {
    self.isLetter || self == "_"
  }

  /// `true` iff `self` is a letter, a decimal digit, or the underscore.
  fileprivate var isIdentifierTail: Bool {
    self.isIdentifierHead || self.isDecimalDigit
  }

  /// `true` iff `self` is an angle bracket.
  fileprivate var isAngleBracket: Bool {
    self == "<" || self == ">"
  }

  /// `true` iff `self` may be part of an operator.
  fileprivate var isOperator: Bool {
    "<>=+-*/%&|!?^~".contains(self)
  }

  /// `true` iff `self` is a decimal digit.
  fileprivate var isDecimalDigit: Bool {
    asciiValue.map({ (ascii) in (0x30 ... 0x39) ~= ascii }) ?? false
  }

}
