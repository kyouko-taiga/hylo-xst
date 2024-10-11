import Utilities

/// The parsing of a source file.
public struct Parser {

  /// The identity of the file into which syntax trees are inserted.
  private var file: Program.SourceFileIdentity

  /// The tokens in the input.
  private var tokens: Lexer

  /// The next token to consume, if already extracted from the source.
  private var lookahead: Token? = nil

  /// The errors that have been collected so far.
  private var errors: [ParseError] = []

  /// The position immediately after the last consumed token.
  private var position: SourcePosition

  /// Creates an instance parsing `source`, inserting syntax trees in `file`.
  public init(_ source: SourceFile, insertingNodesIn file: Program.SourceFileIdentity) {
    self.file = file
    self.tokens = Lexer(tokenizing: source)
    self.position = .init(source.startIndex, in: source)
  }

  // MARK: Declarations

  /// Parses the top-level declarations of a file into `module`.
  public consuming func parseTopLevelDeclarations(
    in module: inout Module
  ) -> [DeclarationIdentity] {
    var ds: [DeclarationIdentity] = []
    while peek() != nil {
      do {
        try ds.append(parseDeclaration(in: &module))
      } catch let e as ParseError {
        report(e)
        recover(at: { ($0.kind == .semicolon) || $0.isDeclarationHead })
      } catch {
        unreachable()
      }
    }
    for e in errors { module.addDiagnostic(.init(e)) }
    return ds
  }

  /// Parses a declaration into `module`.
  ///
  ///     declaration ::=
  ///       associated-type-declaration
  ///       class-declaration
  ///       extension-declaration
  ///       trait-declaration
  ///
  private mutating func parseDeclaration(
    in module: inout Module
  ) throws -> DeclarationIdentity {
    switch peek()?.kind {
    case .type:
      return try .init(parseAssociatedTypeDeclaration(in: &module))
    case .class:
      return try .init(parseClassDeclaration(in: &module))
    case .extension:
      return try .init(parseExtensionDeclaration(in: &module))
    case .fun:
      return try .init(parseFunctionDeclaration(in: &module))
    case .trait:
      return try .init(parseTraitDeclaration(in: &module))
    default:
      throw expected("declaration")
    }
  }

  /// Parses an associated type declaration into `module`.
  ///
  ///     associated-type-declaration ::=
  ///       'type' identifier
  ///
  private mutating func parseAssociatedTypeDeclaration(
    in module: inout Module
  ) throws -> AssociatedTypeDeclaration.ID {
    let introducer = try take(.type) ?? expected("'type'")
    let identifier = parseSimpleIdentifier()

    return module.insert(
      AssociatedTypeDeclaration(
        introducer: introducer,
        identifier: identifier,
        site: introducer.site.extended(upTo: position.index)),
      in: file)
  }

  /// Parses a class declaration into `module`.
  ///
  ///     class-declaration ::=
  ///       'class' identifier type-body
  ///
  private mutating func parseClassDeclaration(
    in module: inout Module
  ) throws -> ClassDeclaration.ID {
    let introducer = try take(.class) ?? expected("'class'")
    let identifier = parseSimpleIdentifier()
    let members = try parseTypeBody(in: &module)

    return module.insert(
      ClassDeclaration(
        introducer: introducer,
        identifier: identifier,
        members: members,
        site: introducer.site.extended(upTo: position.index)),
      in: file)
  }

  /// Parses an extension declaration into `module`.
  ///
  ///     extension-declaration ::=
  ///       'extension' expression type-body
  ///
  private mutating func parseExtensionDeclaration(
    in module: inout Module
  ) throws -> ExtensionDeclaration.ID {
    let introducer = try take(.extension) ?? expected("'extension'")
    let extendee = try parseExpression(in: &module)
    let members = try parseTypeBody(in: &module)

    return module.insert(
      ExtensionDeclaration(
        introducer: introducer,
        extendee: extendee,
        members: members,
        site: introducer.site.extended(upTo: position.index)),
      in: file)
  }

  /// Parses a function declaration into `module`.
  ///
  ///     function-declaration ::=
  ///       'fun' function-identifier parameters
  ///
  private mutating func parseFunctionDeclaration(
    in module: inout Module
  ) throws -> FunctionDeclaration.ID {
    let introducer = try take(.fun) ?? expected("'fun'")
    let identifier = try parseFunctionIdentifier()
    let parameters = try parseParameterList(in: &module)
    let body = try peek()?.kind == .leftBrace ? parseCallableBody(in: &module) : nil

    return module.insert(
      FunctionDeclaration(
        introducer: introducer,
        identifier: identifier,
        parameters: parameters,
        body: body,
        site: introducer.site.extended(upTo: position.index)),
      in: file)
  }

  /// Parses a parenthesized list of parameter declarations into `module`.
  private mutating func parseParameterList(
    in module: inout Module
  ) throws -> [ParameterDeclaration.ID] {
    let (ps, _) = try inParentheses { (m0) in
      try m0.commaSeparated(deimitedBy: .rightParenthesis) { (m1) in
        try m1.parseParameterDeclaration(in: &module)
      }
    }
    return ps
  }

  /// Parses a parameter declaration into `module`.
  ///
  ///     parameter-declaration ::=
  ///       argument-label? identifier (':' expression)? ('=' expression)?
  ///     argument-label ::=
  ///       identifier
  ///       keyword
  ///
  private mutating func parseParameterDeclaration(
    in module: inout Module
  ) throws -> ParameterDeclaration.ID {
    let start = position
    let label: Parsed<String>?
    let identifier: Parsed<String>

    switch (take(if: \.isArgumentLabel), take(.name)) {
    case (let n, .some(let m)):
      identifier = Parsed(String(m.text), at: m.site)
      label = n.map({ (t) in t.kind == .underscore ? nil : Parsed(t) }) ?? identifier

    case (.some(let n), nil):
      if n.isKeyword { report(.init("'\(n.text)' is not a valid identifier", at: n.site)) }
      identifier = Parsed(n)
      label = identifier

    case (nil, nil):
      throw expected("parameter declaration")
    }

    let ascription = try parseOptionalParameterTypeAscription(in: &module)

    return module.insert(
      ParameterDeclaration(
        label: label,
        identifier: identifier,
        ascription: ascription,
        site: .init(start.index ..< position.index, in: tokens.source)),
      in: file)
  }

  /// Parses the body of a function, lambda, or subscript into `module`.
  private mutating func parseCallableBody(in module: inout Module) throws -> CallableBody {
    try inBraces { (me) in
      CallableBody.expression(try me.parseExpression(in: &module))
    }
  }

  /// Parses a trait declaration into `module`.
  ///
  ///     trait-declaration ::=
  ///       'trait' identifier type-body
  ///
  private mutating func parseTraitDeclaration(
    in module: inout Module
  ) throws -> TraitDeclaration.ID {
    let introducer = try take(.trait) ?? expected("'trait'")
    let identifier = parseSimpleIdentifier()
    let members = try parseTypeBody(in: &module)

    return module.insert(
      TraitDeclaration(
        introducer: introducer,
        identifier: identifier,
        members: members,
        site: introducer.site.extended(upTo: position.index)),
      in: file)
  }

  /// Parses a the body of a type declaration into `module`.
  ///
  ///     type-body ::=
  ///       '{' ';'* type-members? '}'
  ///     type-members ::=
  ///       type-members? ';'* declaration ';'*
  ///
  private mutating func parseTypeBody(
    in module: inout Module
  ) throws -> [DeclarationIdentity] {
    try inBraces { (m0) in
      try m0.semicolonSeparated(deimitedBy: .rightBrace) { (m1) in
        try m1.parseDeclaration(in: &module)
      }
    }
  }

  // MARK: Expressions

  /// Parses an expression into `module`.
  private mutating func parseExpression(in module: inout Module) throws -> ExpressionIdentity {
    try parsePrimaryExpression(in: &module)
  }

  /// Parses a primary expression into `module`.
  ///
  ///     primary-expression ::=
  ///       boolean-literal
  ///       integer-literal
  ///       string-literal
  ///       pragma-literal
  ///       buffer-literal
  ///       key-value-literal
  ///       name-expression
  ///       lambda-expression
  ///       conditional-expression
  ///       match-expression
  ///       remote-type-expression
  ///       tuple-expression
  ///       tuple-type-expression
  ///       arrow-type-expression
  ///       '_'
  ///
  private mutating func parsePrimaryExpression(
    in module: inout Module
  ) throws -> ExpressionIdentity {
    switch peek()?.kind {
    case .true, .false:
      return .init(module.insert(BooleanLiteral(site: take()!.site), in: file))
    case .inout, .let, .set, .sink:
      return try .init(parseRemoteTypeExpression(in: &module))
    case .name:
      return try .init(parseUnqualifiedNameExpression(in: &module))
    default:
      throw expected("expression")
    }
  }

  /// Parses a remote type expression into `module`.
  ///
  ///     remote-type-expression ::=
  ///       access-specifier expression
  ///
  private mutating func parseRemoteTypeExpression(
    in module: inout Module
  ) throws -> RemoteTypeExpression.ID {
    let k = parseAccessSpecifcier()
    let e = try parseExpression(in: &module)
    return module.insert(
      RemoteTypeExpression(
        access: k,
        projectee: e,
        site: k.site.extended(upTo: position.index)),
      in: file)
  }

  /// Parses an access specifier.
  ///
  ///     access-specifier ::= (one of)
  ///       let inout set sink
  ///
  private mutating func parseAccessSpecifcier() -> Parsed<AccessEffect> {
    switch peek()?.kind {
    case .let:
      return Parsed(.let, at: take()!.site)
    case .inout:
      return Parsed(.inout, at: take()!.site)
    case .set:
      return Parsed(.set, at: take()!.site)
    case .sink:
      return Parsed(.sink, at: take()!.site)
    default:
      return fix(expected("access specifier"), with: Parsed(.let, at: .empty(at: position)))
    }
  }

  /// Parses an unqualified name expression into `module`.
  private mutating func parseUnqualifiedNameExpression(
    in module: inout Module
  ) throws -> NameExpression.ID {
    let identifier = try take(.name) ?? expected("identifier")

    return module.insert(
      NameExpression(
        qualification: .none,
        name: .init(Name(identifier: String(identifier.text)), at: identifier.site),
        site: identifier.site),
      in: file)
  }

  /// Parses a type ascription into `module` iff the next token is a colon.
  ///
  ///     type-ascription ::=
  ///       ':' expr
  ///
  private mutating func parseOptionalTypeAscription(
    in module: inout Module
  ) throws -> ExpressionIdentity? {
    if take(.colon) != nil {
      return try parseExpression(in: &module)
    } else {
      return nil
    }
  }

  /// Parses the type ascription of a parameter into `module` iff the next token is a colon.
  private mutating func parseOptionalParameterTypeAscription(
    in module: inout Module
  ) throws -> RemoteTypeExpression.ID? {
    switch try parseOptionalTypeAscription(in: &module) {
    case nil:
      return nil
    case .some(let b) where module.kind(of: b) == RemoteTypeExpression.self:
      return .init(rawValue: b.rawValue)
    case .some(let b):
      let s = module[b.rawValue].site
      let k = Parsed<AccessEffect>(.let, at: .empty(at: s.start))
      return module.insert(RemoteTypeExpression(access: k, projectee: b, site: s), in: file)
    }
  }

  // MARK: Identifiers

  /// Parses a function identifier.
  ///
  ///     function-identider ::=
  ///       identifier
  ///       operator-identifier
  ///
  private mutating func parseFunctionIdentifier(
  ) throws -> Parsed<FunctionDeclaration.Identifier> {
    if let t = peek() {
      if t.isOperatorNotation {
        return try parseOperatorIdentifier()
      } else if t.isOperator {
        report(.init("missing operator notation", at: .empty(at: t.site.start)))
        let identifier = try parseOperator()
        return .init(.operator(.none, String(identifier.text)), at: identifier)
      }
    }

    let identifier = parseSimpleIdentifier()
    return .init(.simple(identifier.value), at: identifier.site)
  }

  /// Parses an operator identifier into `module`.
  ///
  ///     operator-identifier ::= (token)
  ///       operator-notation operator
  ///
  private mutating func parseOperatorIdentifier(
  ) throws -> Parsed<FunctionDeclaration.Identifier> {
    let head = try take(if: \.isOperatorNotation) ?? expected("operator notation")
    let notation: OperatorNotation = switch head.kind {
    case .infix: .infix
    case .postfix: .postfix
    case .prefix: .postfix
    default: unreachable()
    }

    let identifier = try parseOperator()
    if head.site.end != identifier.start {
      report(.init("illegal space between after operator notation", at: identifier))
    }

    return .init(
      .operator(notation, String(identifier.text)),
      at: head.site.extended(toCover: identifier))
  }

  /// Parses an operator and returns the region of the file from which it has been extracted.
  private mutating func parseOperator() throws -> SourceSpan {
    // Single-token operators.
    if let t = take(oneOf: [.ampersand, .equal, .operator]) {
      return t.site
    }

    // Multi-token operators.
    let first = try take(oneOf: [.leftAngle, .rightAngle]) ?? expected("operator")
    var last = first
    while let u = peek(), u.site.region.lowerBound == last.site.region.upperBound {
      if let next = take(if: \.isOperator) {
        last = next
      } else {
        break
      }
    }
    return first.site.extended(toCover: last.site)
  }

  /// Parses a simple identifier.
  private mutating func parseSimpleIdentifier() -> Parsed<String> {
    if let n = take(.name) {
      return .init(String(n.text), at: n.site)
    } else {
      report(expected("identifier"))
      return .init("#?", at: .empty(at: position))
    }
  }

  // MARK: Helpers

  /// Parses an instance of `T` or restores `self` to its current state if that fails.
  private mutating func attempt<T>(_ parse: (inout Self) throws -> T) -> T? {
    var backup = self
    do {
      return try parse(&self)
    } catch {
      swap(&self, &backup)
      return nil
    }
  }

  /// Parses an instance of `T` enclosed in `delimiters`.
  private mutating func between<T>(
    _ delimiters: (left: Token.Kind, right: Token.Kind),
    _ parse: (inout Self) throws -> T
  ) throws -> T {
    _ = try take(delimiters.left) ?? expected(delimiters.left.errorDescription)
    do {
      let contents = try parse(&self)
      if take(delimiters.right) == nil { report(expected(delimiters.right.errorDescription)) }
      return contents
    } catch let e as ParseError {
      recover(at: { _ in false })
      if take(.rightBrace) == nil { report(expected(delimiters.right.errorDescription)) }
      throw e
    }
  }

  /// Parses an instance of `T` enclosed in braces.
  private mutating func inBraces<T>(_ parse: (inout Self) throws -> T) throws -> T {
    try between((.leftBrace, .rightBrace), parse)
  }

  /// Parses an instance of `T` enclosed in parentheses.
  private mutating func inParentheses<T>(_ parse: (inout Self) throws -> T) throws -> T {
    try between((.leftParenthesis, .rightParenthesis), parse)
  }

  /// parses a list of instances of `T` separated by colons.
  private mutating func commaSeparated<T>(
    deimitedBy rightDelimiter: Token.Kind?, _ parse: (inout Self) throws -> T
  ) throws -> ([T], lastComma: Token?) {
    var xs: [T] = []
    var lastComma: Token? = nil
    while let head = peek() {
      if head.kind == rightDelimiter { break }
      do {
        try xs.append(parse(&self))
      } catch let e as ParseError {
        report(e)
        recover(at: { (t) in t.kind == rightDelimiter || t.kind == .comma })
      }
      if let c = take(.comma) { lastComma = c }
    }
    return (xs, lastComma)
  }

  /// parses a list of instances of `T` separated by semicolons.
  private mutating func semicolonSeparated<T>(
    deimitedBy rightDelimiter: Token.Kind?, _ parse: (inout Self) throws -> T
  ) throws -> [T] {
    var xs: [T] = []
    while let head = peek() {
      discard(while: { $0.kind == .semicolon })
      if head.kind == rightDelimiter { break }
      do {
        try xs.append(parse(&self))
      } catch let e as ParseError {
        report(e)
        recover(at: { (t) in t.kind == rightDelimiter || t.kind == .semicolon })
      }
    }
    return xs
  }

  /// Returns `true` iff there is a whitespace at the current position.
  private func whitespaceAtCurrentPosition() -> Bool {
    tokens.source[position.index].isWhitespace
  }

  /// Returns the next token without consuming it.
  private mutating func peek() -> Token? {
    if lookahead == nil { lookahead = tokens.next() }
    return lookahead
  }

  /// Consumes and returns the next token.
  private mutating func take() -> Token? {
    let next = lookahead.take() ?? tokens.next()
    position = next?.site.end ?? .init(tokens.source.endIndex, in: tokens.source)
    return next
  }

  /// Consumes and returns the next token iff it has kind `k`; otherwise, returns `nil`.
  private mutating func take(_ k: Token.Kind) -> Token? {
    peek()?.kind == k ? take() : nil
  }

  /// Consumes and returns the next token iff it satisifies `predicate`; otherwise, returns `nil`.
  private mutating func take(if predicate: (Token) -> Bool) -> Token? {
    if let t = peek(), predicate(t) {
      return take()
    } else {
      return nil
    }
  }

  /// Consumes and returns the next token iff its kind is in `ks`; otherwise, returns `nil`.
  private mutating func take<T: Collection<Token.Kind>>(oneOf ks: T) -> Token? {
    take(if: { (t) in ks.contains(t.kind) })
  }

  /// Discards tokens until `predicate` isn't satisfied or all the input has been consumed.
  private mutating func discard(while predicate: (Token) -> Bool) {
    while let t = peek(), predicate(t) { _ = take() }
  }

  /// Discards tokens until the next token may be at the beginning of a top-level declaration.
  private mutating func discardUntilNextTopLevelDeclaration() {
    recover(at: { $0.isDeclarationHead })
  }

  /// Discards token until `predicate` is satisfied or the next token is a unbalanced delimiter.
  private mutating func recover(at predicate: (Token) -> Bool) {
    var nesting = 0
    while let t = peek(), !predicate(t) {
      switch t.kind {
      case .leftBrace:
        nesting += 1
      case .rightBrace:
        if nesting == 0 { return } else { nesting -= 1 }
      default:
         break
      }
      _ = take()
    }
  }

  /// Returns a parse error explaining that `s` was expected at the current position.
  private func expected(_ s: String) -> ParseError {
    .init("expected \(s)", at: .empty(at: position))
  }

  /// Reports `e` and returns `v`.
  private mutating func fix<T>(_ e: ParseError, with v: T) -> T {
    report(e)
    return v
  }

  /// Reports `e`.
  private mutating func report(_ e: ParseError) {
    errors.append(e)
  }

}

/// An error that occurred during parsing.
public struct ParseError: Error, CustomStringConvertible {

  /// A description of the error that occurred.
  public let description: String

  /// The source code or source position (if empty) identified as the cause of the error.
  public let site: SourceSpan

  /// Creates an instance reporting `problem` at `site`.
  public init(_ problem: String, at site: SourceSpan) {
    self.description = problem
    self.site = site
  }

}

extension Diagnostic {

  /// Creates a diagnostic describing `e`.
  fileprivate init(_ e: ParseError) {
    self.init(.error, e.description, at: e.site)
  }

}

extension Parsed<String> {

  /// Creates an instance with the text of `t`.
  fileprivate init(_ t: Token) {
    self.init(String(t.text), at: t.site)
  }

}

extension Token.Kind {

  /// Returns a description of `self` for error reporting.
  fileprivate var errorDescription: String {
    switch self {
    case .colon: "':'"
    case .leftAngle: "'<'"
    case .rightAngle: "'>'"
    case .leftBrace: "'{'"
    case .rightBrace: "'}'"
    case .leftBracket: "'['"
    case .rightBracket: "']'"
    case .leftParenthesis: "'('"
    case .rightParenthesis: "')'"
    default: "\(self)"
    }
  }

}
