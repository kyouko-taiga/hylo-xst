/// The tokens of a source file.
public struct Lexer: IteratorProtocol, Sequence {

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
    } else if head.isOperator {
      return takeOperator()
    } else {
      return takePunctuationOrDelimiter()
    }
  }

  /// Consumes and returns a keyword or identifier.
  private mutating func takeKeywordOrIdentifier() -> Token {
    let word = take(while: \.isIdentifierTail)
    let kind: Token.Kind
    switch word {
    case "_": kind = .underscore
    case "conformance": kind = .conformance
    case "extension": kind = .extension
    case "false": kind = .false
    case "fun": kind = .fun
    case "import": kind = .import
    case "infix": kind = .infix
    case "init": kind = .`init`
    case "inout": kind = .inout
    case "internal": kind = .internal
    case "let": kind = .let
    case "postfix": kind = .postfix
    case "prefix": kind = .prefix
    case "private": kind = .private
    case "public": kind = .public
    case "return": kind = .return
    case "set": kind = .set
    case "sink": kind = .sink
    case "struct": kind = .struct
    case "trait": kind = .trait
    case "true": kind = .true
    case "type": kind = .type
    case "typealias": kind = .typealias
    case "var": kind = .var
    default: kind = .name
    }
    assert(!word.isEmpty)
    return .init(kind: kind, site: span(word.startIndex ..< word.endIndex))
  }

  /// Consumes and returns an operator.
  private mutating func takeOperator() -> Token {
    // Leading angle brackets are tokenized individually, to parse generic clauses.
    if peek()!.isAngleBracket {
      return takePunctuationOrDelimiter()
    }

    let text = take(while: \.isOperator)
    let kind: Token.Kind
    switch text {
    case "&": kind = .ampersand
    case "=": kind = .assign
    case "->": kind = .arrow
    case "==": kind = .equal
    default: kind = .operator
    }
    return .init(kind: kind, site: span(text.startIndex ..< text.endIndex))
  }

  /// Consumes and returns a punctuation token if the input starts with a punctuation symbol;
  /// otherwise consumes a single character and returns an error token.
  private mutating func takePunctuationOrDelimiter() -> Token {
    let start = position
    let kind: Token.Kind
    switch take() {
    case "<": kind = .leftAngle
    case ">": kind = .rightAngle
    case "{": kind = .leftBrace
    case "}": kind = .rightBrace
    case "[": kind = .leftBracket
    case "]": kind = .rightBracket
    case "(": kind = .leftParenthesis
    case ")": kind = .rightParenthesis
    case ",": kind = .comma
    case ".": kind = .dot
    case ";": kind = .semicolon
    case ":": kind = take(":") == nil ? .colon : .doubleColon
    default: kind = .error
    }
    return .init(kind: kind, site: span(start ..< position))
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
            return .init(kind: .unterminatedBlockComment, site: span(start ..< position))
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
