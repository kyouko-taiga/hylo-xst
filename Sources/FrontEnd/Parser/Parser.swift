import Utilities

/// The parsing of a source file.
public struct Parser {

  /// The tokens in the input.
  private var tokens: Lexer

  /// The next token to consume, if already extracted from the source.
  private var lookahead: Token? = nil

  /// The errors that have been collected so far.
  private var errors: [ParseError] = []

  /// The position immediately after the last consumed token.
  private var position: SourcePosition

  /// `true` iff we're parsing the subpattern of binding pattern.
  private var isParsingBindingSubpattern = false

  /// Creates an instance parsing `source`.
  public init(_ source: SourceFile) {
    self.tokens = Lexer(tokenizing: source)
    self.position = .init(source.startIndex, in: source)
  }

  // MARK: Declarations

  /// Parses the top-level declarations of a file.
  internal consuming func parseTopLevelDeclarations(in file: inout Module.SourceContainer) {
    assert(file.roots.isEmpty)
    var roots: [DeclarationIdentity] = []
    while peek() != nil {
      do {
        try roots.append(parseDeclaration(in: &file))
      } catch let e as ParseError {
        report(e)
        recover(at: { ($0.tag == .semicolon) || $0.isDeclarationHead })
      } catch {
        unreachable()
      }
    }
    for e in errors { file.addDiagnostic(.init(e)) }
    swap(&file.roots, &roots)
  }

  /// Parses a declaration.
  ///
  ///     declaration ::=
  ///       associated-type-declaration
  ///       binding-declaration
  ///       conformance-declaration
  ///       extension-declaration
  ///       struct-declaration
  ///       trait-declaration
  ///
  private mutating func parseDeclaration(
    in file: inout Module.SourceContainer
  ) throws -> DeclarationIdentity {
    guard let head = peek() else { throw expected("declaration") }

    switch head.tag {
    case .inout, .let, .set, .sink, .var:
      return try .init(parseBindingDeclaration(in: &file))
    case .given:
      return try .init(parseConformanceDeclaration(in: &file))
    case .extension:
      return try .init(parseExtensionDeclaration(in: &file))
    case .fun:
      return try .init(parseFunctionDeclaration(in: &file))
    case .`init`:
      return try .init(parseInitializerDeclaration(in: &file))
    case .struct:
      return try .init(parseStructDeclaration(in: &file))
    case .trait:
      return try .init(parseTraitDeclaration(in: &file))
    case .type:
      return try .init(parseAssociatedTypeDeclaration(in: &file))
    case .typealias:
      return try .init(parseTypeAliasDeclaration(in: &file))
    case .name where head.text == "memberwise":
      return try .init(parseInitializerDeclaration(in: &file))
    default:
      throw expected("declaration", at: .empty(at: head.site.start))
    }
  }

  /// Parses an associated type declaration.
  ///
  ///     associated-type-declaration ::=
  ///       'type' identifier
  ///
  private mutating func parseAssociatedTypeDeclaration(
    in file: inout Module.SourceContainer
  ) throws -> AssociatedTypeDeclaration.ID {
    let introducer = try take(.type) ?? expected("'type'")
    let identifier = parseSimpleIdentifier()

    return file.insert(
      AssociatedTypeDeclaration(
        introducer: introducer,
        identifier: identifier,
        site: span(from: introducer)))
  }

  /// Parses a binding declaration.
  ///
  ///     binding-declaration ::=
  ///       binding-pattern ('=' expression)?
  ///
  private mutating func parseBindingDeclaration(
    in file: inout Module.SourceContainer
  ) throws -> BindingDeclaration.ID {
    let b = try parseBindingPattern(in: &file)
    let i = try parseOptionalInitializer(in: &file)

    return file.insert(
      BindingDeclaration(
        pattern: b, initializer: i,
        site: span(from: file[b].site.start)))
  }

  /// Parses an initializer/default expression iff the next token an equal sign.
  ///
  ///     initializer-expression ::=
  ///       '=' expression
  ///
  private mutating func parseOptionalInitializer(
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity? {
    if take(.assign) != nil {
      return try parseExpression(in: &file)
    } else {
      return nil
    }
  }

  /// Parses a conformance declaration.
  ///
  ///     conformance-declaration ::=
  ///       'given' expression ':' expression type-body
  ///
  private mutating func parseConformanceDeclaration(
    in file: inout Module.SourceContainer
  ) throws -> ConformanceDeclaration.ID {
    let introducer = try take(.given) ?? expected("'given'")
    let staticParameters = try parseOptionalCompileTimeParameters(in: &file)
    let extendee = try parseExpression(in: &file)
    _ = try take(.colon) ?? expected("':'")
    let concept = try parseExpression(in: &file)
    let members = try parseTypeBody(in: &file)

    return file.insert(
      ConformanceDeclaration(
        introducer: introducer,
        staticParameters: staticParameters,
        extendee: extendee,
        concept: concept,
        members: members,
        site: span(from: introducer)))
  }

  /// Parses an extension declaration.
  ///
  ///     extension-declaration ::=
  ///       'extension' expression type-body
  ///
  private mutating func parseExtensionDeclaration(
    in file: inout Module.SourceContainer
  ) throws -> ExtensionDeclaration.ID {
    let introducer = try take(.extension) ?? expected("'extension'")
    let staticParameters = try parseOptionalCompileTimeParameters(in: &file)
    let extendee = try parseExpression(in: &file)
    let members = try parseTypeBody(in: &file)

    return file.insert(
      ExtensionDeclaration(
        introducer: introducer,
        staticParameters: staticParameters,
        extendee: extendee,
        members: members,
        site: span(from: introducer)))
  }

  /// Parses a function declaration.
  ///
  ///     function-declaration ::=
  ///       'fun' function-identifier parameter-clauses return-type-ascription? callable-body?
  ///     parameter-clauses ::=
  ///       compile-time-parameters? run-time-parameters
  ///
  private mutating func parseFunctionDeclaration(
    in file: inout Module.SourceContainer
  ) throws -> FunctionDeclaration.ID {
    let introducer = try take(.fun) ?? expected("'fun'")
    let identifier = try parseFunctionIdentifier()
    let staticParameters = try parseOptionalCompileTimeParameters(in: &file)
    let runtimeParameters = try parseParenthesizedParameterList(in: &file)
    let effect = parseOptionalAccessEffect() ?? Parsed(.let, at: .empty(at: position))
    let output = try parseOptionalReturnTypeAscription(in: &file)
    let body = try parseOptionalCallableBody(in: &file)

    return file.insert(
      FunctionDeclaration(
        introducer: introducer,
        identifier: identifier,
        staticParameters: staticParameters,
        parameters: runtimeParameters,
        effect: effect,
        output: output,
        body: body,
        site: introducer.site.extended(upTo: position.index)))
  }

  /// Parses a compile-time parameter list iff the next token is a left angle bracket. Otherwise,
  /// returns an empty list.
  ///
  ///     compile-time-parameters ::=
  ///       '<' generic-parameters where-clause? '>'
  ///
  private mutating func parseOptionalCompileTimeParameters(
    in file: inout Module.SourceContainer
  ) throws -> StaticParameters {
    guard let start = peek(), start.tag == .leftAngle else {
      return .empty(at: .empty(at: position))
    }

    return try inAngles { (me) in
      let xs = try me.parseCommaSeparatedGenericParameters(in: &file)
      let ys = try me.parseOptionalWhereClause(in: &file)
      return StaticParameters(explicit: xs, implicit: ys, site: me.span(from: start))
    }
  }

  /// Parses the generic parameter declarations of a context clause.
  private mutating func parseCommaSeparatedGenericParameters(
    in file: inout Module.SourceContainer
  ) throws -> [GenericParameterDeclaration.ID] {
    let (ps, _) = try commaSeparated(delimitedBy: Token.oneOf([.rightAngle, .where])) { (me) in
      try me.parseGenericParameterDeclaration(in: &file)
    }
    return ps
  }

  /// Parses a generic parameter declaration.
  private mutating func parseGenericParameterDeclaration(
    in file: inout Module.SourceContainer
  ) throws -> GenericParameterDeclaration.ID {
    let n = try take(.name) ?? expected("identifier")
    return file.insert(GenericParameterDeclaration(identifier: .init(n), site: n.site))
  }

  /// Parses a where clause iff the next token is `.where`. Otherwise, returns an empty clause.
  private mutating func parseOptionalWhereClause(
    in file: inout Module.SourceContainer
  ) throws -> [DeclarationIdentity] {
    guard take(.where) != nil else { return [] }
    let (ps, _) = try commaSeparated(delimitedBy: .rightAngle) { (me) in
      try me.parseContextParameter(in: &file)
    }
    return ps
  }

  /// Parses an implicit compile-time context parameter.
  private mutating func parseContextParameter(
    in file: inout Module.SourceContainer
  ) throws -> DeclarationIdentity {
    let l = try parseCompoundExpression(in: &file)
    let s = try take(.colon) ?? take(.equal) ?? expected("':' or '=='")
    let r = try parseCompoundExpression(in: &file)

    let d = file.insert(
      UsingDeclaration(
        lhs: l, rhs: r,
        semantics: .init((s.tag == .colon) ? .conformance : .equality, at: s.site),
        site: file[l].site.extended(toCover: file[r].site)))
    return .init(d)
  }

  /// Parses an initializer declaration.
  ///
  ///     initializer-declaration ::=
  ///       'memberwise' 'init'
  ///       'init' parameters callable-body?
  ///
  private mutating func parseInitializerDeclaration(
    in file: inout Module.SourceContainer
  ) throws -> InitializerDeclaration.ID {
    // Memberwise initializer?
    if let head = take(contextual: "memberwise") {
      let t = take(.`init`) ?? fix(expected("'init'"), with: head)
      let i = InitializerDeclaration.Introducer.memberwiseinit
      let s = head.site.extended(toCover: t.site)

      return file.insert(
        InitializerDeclaration(
          introducer: .init(i, at: s), parameters: [], body: nil,
          site: s))
    }

    // Regular initializer?
    else if let head = take(.`init`) {
      let parameters = try parseParenthesizedParameterList(in: &file)
      let body = try parseOptionalCallableBody(in: &file)

      return file.insert(
        InitializerDeclaration(
          introducer: .init(.`init`, at: head.site), parameters: parameters, body: body,
          site: head.site.extended(upTo: position.index)))
    }

    // Missing introducer.
    else { throw expected("'init'") }
  }

  /// Parses a parenthesized list of parameter declarations.
  private mutating func parseParenthesizedParameterList(
    in file: inout Module.SourceContainer
  ) throws -> [ParameterDeclaration.ID] {
    let (ps, _) = try inParentheses { (m0) in
      try m0.commaSeparated(delimitedBy: .rightParenthesis) { (m1) in
        try m1.parseParameterDeclaration(in: &file)
      }
    }
    return ps
  }

  /// Parses a parameter declaration.
  ///
  ///     parameter-declaration ::=
  ///       expression-label? identifier (':' expression)? ('=' expression)?
  ///     expression-label ::=
  ///       identifier
  ///       keyword
  ///
  private mutating func parseParameterDeclaration(
    in file: inout Module.SourceContainer
  ) throws -> ParameterDeclaration.ID {
    let start = position
    let label: Parsed<String>?
    let identifier: Parsed<String>

    switch (take(if: \.isArgumentLabel), take(.name)) {
    case (let n, .some(let m)):
      identifier = Parsed(String(m.text), at: m.site)
      label = n.map({ (t) in t.tag == .underscore ? nil : Parsed(t) }) ?? identifier

    case (.some(let n), nil):
      if n.isKeyword { report(.init("'\(n.text)' is not a valid identifier", at: n.site)) }
      identifier = Parsed(n)
      label = identifier

    case (nil, nil):
      throw expected("parameter declaration")
    }

    let ascription = try parseOptionalParameterTypeAscription(in: &file)
    let defaultValue = try parseOptionalInitializer(in: &file)

    return file.insert(
      ParameterDeclaration(
        label: label,
        identifier: identifier,
        ascription: ascription,
        default: defaultValue,
        site: span(from: start)))
  }

  /// Parses the body of a callable abstraction iff the next token is a left brace.
  private mutating func parseOptionalCallableBody(
    in file: inout Module.SourceContainer
  ) throws -> [StatementIdentity]? {
    try peek()?.tag == .leftBrace ? parseCallableBody(in: &file) : nil
  }

  /// Parses the body of a function, lambda, or subscript.
  private mutating func parseCallableBody(
    in file: inout Module.SourceContainer
  ) throws -> [StatementIdentity] {
    try inBraces { (m0) in
      try m0.semicolonSeparated(delimitedBy: .rightBrace) { (m1) in
        try m1.parseStatement(in: &file)
      }
    }
  }

  /// Parses a struct declaration.
  ///
  ///     struct-declaration ::=
  ///       'struct' identifier type-body
  ///
  private mutating func parseStructDeclaration(
    in file: inout Module.SourceContainer
  ) throws -> StructDeclaration.ID {
    let introducer = try take(.struct) ?? expected("'struct'")
    let identifier = parseSimpleIdentifier()
    let staticParameters = try parseOptionalCompileTimeParameters(in: &file)
    let members = try parseTypeBody(in: &file)

    return file.insert(
      StructDeclaration(
        introducer: introducer,
        identifier: identifier,
        staticParameters: staticParameters,
        members: members,
        site: span(from: introducer)))
  }

  /// Parses a trait declaration.
  ///
  ///     trait-declaration ::=
  ///       'trait' identifier type-body
  ///
  private mutating func parseTraitDeclaration(
    in file: inout Module.SourceContainer
  ) throws -> TraitDeclaration.ID {
    let introducer = try take(.trait) ?? expected("'trait'")
    let identifier = parseSimpleIdentifier()
    let members = try parseTypeBody(in: &file)

    let conformer = file.insert(
      GenericParameterDeclaration(
        identifier: .init("Self", at: identifier.site), site: identifier.site))

    return file.insert(
      TraitDeclaration(
        introducer: introducer,
        identifier: identifier,
        parameters: [conformer],
        members: members,
        site: span(from: introducer)))
  }

  /// Parses a the body of a type declaration.
  ///
  ///     type-body ::=
  ///       '{' ';'* type-members? '}'
  ///     type-members ::=
  ///       type-members? ';'* declaration ';'*
  ///
  private mutating func parseTypeBody(
    in file: inout Module.SourceContainer
  ) throws -> [DeclarationIdentity] {
    try inBraces { (m0) in
      try m0.semicolonSeparated(delimitedBy: .rightBrace) { (m1) in
        try m1.parseDeclaration(in: &file)
      }
    }
  }

  /// Parses a type alias declaration.
  ///
  ///     type-alias-declaration ::=
  ///       'typealias' identifier '=' expression
  ///
  private mutating func parseTypeAliasDeclaration(
    in file: inout Module.SourceContainer
  ) throws -> TypeAliasDeclaration.ID {
    let introducer = try take(.typealias) ?? expected("'typealias'")
    let identifier = parseSimpleIdentifier()
    _ = try take(.assign) ?? expected("'='")
    let aliasee = try parseExpression(in: &file)

    return file.insert(
      TypeAliasDeclaration(
        introducer: introducer,
        identifier: identifier,
        aliasee: aliasee,
        site: introducer.site.extended(upTo: position.index)))
  }

  /// Parses a variable declaration.
  private mutating func parseVariableDeclaration(
    in file: inout Module.SourceContainer
  ) throws -> VariableDeclaration.ID {
    let n = try take(.name) ?? expected("identifier")
    return file.insert(VariableDeclaration(identifier: .init(n)))
  }

  // MARK: Expressions

  /// Parses an expression.
  private mutating func parseExpression(
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity {
    try parseInfixExpression(in: &file)
  }

  /// Parses the root of infix expression whose operator binds at least as tightly as `p`.
  private mutating func parseInfixExpression(
    minimumPrecedence p: PrecedenceGroup = .assignment, in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity {
    var l = try parseConversionExpression(in: &file)

    while p < .max {
      guard let h = peek(), h.isOperator, whitespaceBeforeNextToken() else { break }
      guard let (o, q) = try parseInfixOperator(notTighterThan: p) else { break }

      if !whitespaceBeforeNextToken() {
        report(.init("infix operator requires whitespaces on both sides", at: .empty(at: o.end)))
      }

      let r = try parseInfixExpression(minimumPrecedence: q.next, in: &file)
      let f = file.insert(
        NameExpression(
          qualification: .explicit(l),
          name: .init(Name(identifier: String(o.text), notation: .infix), at: o),
          site: o))
      let n = file.insert(
        Call(
          callee: .init(f),
          arguments: [.init(label: nil, value: r)],
          style: .parenthesized,
          site: file[l].site.extended(upTo: position.index)))
      l = .init(n)
    }

    return l
  }

  /// Parses an expression possibly wrapped in a conversion.
  private mutating func parseConversionExpression(
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity {
    let l = try parsePrefixExpression(in: &file)
    guard let o = take(.conversion) else { return l }

    let r = try parseExpression(in: &file)
    let n = file.insert(
      Conversion(
        source: l, target: r, semantics: .init(o.text)!,
        site: file[l].site.extended(upTo: position.index)))
    return .init(n)
  }

  /// Parses an expression possibly prefixed by an operator
  private mutating func parsePrefixExpression(
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity {
    try parseCompoundExpression(in: &file)
  }

  /// Parses an expression made of one or more components.
  ///
  ///     compound-expression ::=
  ///       compound-expression-head
  ///       compound-expression '.' (unqualified-name-expression | decimal-number)
  ///
  private mutating func parseCompoundExpression(
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity {
    var head = try parsePrimaryExpression(in: &file)

    while true {
      if try appendNominalComponent(to: &head, in: &file) { continue }

      // Exit if there's a whitespace before the next token.
      if whitespaceBeforeNextToken() { break }

      if try appendParenthesizedArguments(to: &head, in: &file) { continue }
      if try appendAngledArguments(to: &head, in: &file) { continue }
      break
    }

    return head
  }

  /// If the next token is a dot, parses a nominal component, assigns `h` to a name expression
  /// qualified by its current value and returns `true`. Otherwise, returns `false`.
  private mutating func appendNominalComponent(
    to h: inout ExpressionIdentity, in file: inout Module.SourceContainer
  ) throws -> Bool {
    if take(.dot) == nil { return false }
    let n = try parseNominalComponent()
    let s = span(from: file[h].site.start)
    let m = file.insert(NameExpression(qualification: .explicit(h), name: n, site: s))
    h = .init(m)
    return true
  }

  /// If the next token is a left parenthesis, parses an argument list, assigns `h` to a call
  /// expression applying its current value, and returns `true`. Otherwise, returns `false`.
  private mutating func appendParenthesizedArguments(
    to h: inout ExpressionIdentity, in file: inout Module.SourceContainer
  ) throws -> Bool {
    if peek()?.tag != .leftParenthesis { return false }
    let (a, _) = try inParentheses { (me) in
      try me.parseLabeledExpressionList(delimitedBy: .rightParenthesis, in: &file)
    }
    let s = file[h].site.extended(upTo: position.index)
    let m = file.insert(Call(callee: h, arguments: a, style: .parenthesized, site: s))
    h = .init(m)
    return true
  }

  /// If the next token is a left angle, parses an argument list, assigns `h` to a static call
  /// expression applying its current value, and returns `true`. Otherwise, returns `false`.
  private mutating func appendAngledArguments(
    to h: inout ExpressionIdentity, in file: inout Module.SourceContainer
  ) throws -> Bool {
    if peek()?.tag != .leftAngle { return false }
    let (a, _) = try inAngles { (m0) in
      try m0.commaSeparated(delimitedBy: .rightAngle) { (m1) in
        try m1.parseExpression(in: &file)
      }
    }
    let s = file[h].site.extended(upTo: position.index)
    let m = file.insert(StaticCall(callee: h, arguments: a, site: s))
    h = .init(m)
    return true
  }

  /// Parses a list of labeled expressions.
  ///
  ///     labeled-expression-list ::=
  ///       labeled-expression (',' labeled-expression)* ','?
  ///     labeled-expression ::=
  ///       (expression-label ':')? expression
  ///
  private mutating func parseLabeledExpressionList(
    delimitedBy rightDelimiter: Token.Tag,
    in file: inout Module.SourceContainer
  ) throws -> ([LabeledExpression], lastComma: Token?) {
    try labeledSyntaxList(delimitedBy: rightDelimiter) { (me) in
      try me.parseExpression(in: &file)
    }
  }

  /// Parses a primary expression.
  ///
  ///     primary-expression ::=
  ///       boolean-literal
  ///       buffer-literal
  ///       integer-literal
  ///       key-value-literal
  ///       pragma-literal
  ///       string-literal
  ///       tuple-literal
  ///       name-expression
  ///       lambda-expression
  ///       conditional-expression
  ///       match-expression
  ///       remote-type-expression
  ///       tuple-type-expression
  ///       arrow-type-expression
  ///       '_'
  ///
  private mutating func parsePrimaryExpression(
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity {
    switch peek()?.tag {
    case .true, .false:
      return .init(file.insert(BooleanLiteral(site: take()!.site)))
    case .inout, .let, .set, .sink:
      return try .init(parseRemoteTypeExpression(in: &file))
    case .name:
      return try .init(parseUnqualifiedNameExpression(in: &file))
    case .leftBrace:
      return try .init(parseTupleTypeExpression(in: &file))
    case .leftParenthesis:
      return try parseTupleLiteralOrParenthesizedExpression(in: &file)
    case .underscore:
      return try .init(parseWildcardTypeLiteral(in: &file))
    default:
      throw expected("expression")
    }
  }

  /// Parses a remote type expression.
  ///
  ///     remote-type-expression ::=
  ///       access-effect expression
  ///
  private mutating func parseRemoteTypeExpression(
    in file: inout Module.SourceContainer
) throws -> RemoteTypeExpression.ID {
    let k = parseAccessEffect()
    let e = try parseExpression(in: &file)
    return file.insert(
      RemoteTypeExpression(access: k, projectee: e, site: k.site.extended(upTo: position.index)))
  }

  /// Parses an access effect.
  ///
  ///     access-effect ::= (one of)
  ///       let inout set sink
  ///
  private mutating func parseAccessEffect() -> Parsed<AccessEffect> {
    if let k = parseOptionalAccessEffect() {
      return k
    } else {
      return fix(expected("access specifier"), with: Parsed(.let, at: .empty(at: position)))
    }
  }

  /// Parses an access effect iff the next token denotes one.
  private mutating func parseOptionalAccessEffect() -> Parsed<AccessEffect>? {
    switch peek()?.tag {
    case .let:
      return Parsed(.let, at: take()!.site)
    case .inout:
      return Parsed(.inout, at: take()!.site)
    case .set:
      return Parsed(.set, at: take()!.site)
    case .sink:
      return Parsed(.sink, at: take()!.site)
    default:
      return nil
    }
  }

  /// Parses an unqualified name expression.
  ///
  ///     unqualified-name-expression ::=
  ///       identifier
  ///
  private mutating func parseUnqualifiedNameExpression(
    in file: inout Module.SourceContainer
  ) throws -> NameExpression.ID {
    let name = try parseNominalComponent()
    return file.insert(NameExpression(qualification: .none, name: name, site: name.site))
  }

  /// Parses a name and its optional compile-time arguments.
  private mutating func parseNominalComponent() throws -> Parsed<Name> {
    let identifier = try take(.name) ?? expected("identifier")
    return .init(Name(identifier: String(identifier.text)), at: identifier.site)
  }

  /// Parses a tuple type expression.
  ///
  ///     tuple-type-expression ::=
  ///       '{' tuple-type-body? '}'
  ///     tuple-type-body ::=
  ///       labeled-expression (',' labeled-expression)*
  ///
  private mutating func parseTupleTypeExpression(
    in file: inout Module.SourceContainer
  ) throws -> TupleTypeExpression.ID {
    let start = try peek() ?? expected("'{'")
    let (elements, _) = try inBraces { (me) in
      try me.parseLabeledExpressionList(delimitedBy: .rightBrace, in: &file)
    }

    return file.insert(
      TupleTypeExpression(elements: elements, site: start.site.extended(upTo: position.index)))
  }

  /// Parses a tuple literal or a parenthesized expression.
  ///
  ///     tuple-literal ::=
  ///       '(' tuple-literal-body? ')'
  ///     tuple-literal-body ::=
  ///       labeled-expression (',' labeled-expression)*
  ///
  private mutating func parseTupleLiteralOrParenthesizedExpression(
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity {
    let start = try peek() ?? expected("'('")
    let (elements, lastComma) = try inParentheses { (me) in
      try me.parseLabeledExpressionList(delimitedBy: .rightParenthesis, in: &file)
    }

    if (elements.count == 1) && (elements[0].label == nil) && (lastComma == nil) {
      return elements[0].value
    } else {
      let t = file.insert(
        TupleLiteral(elements: elements, site: start.site.extended(upTo: position.index)))
      return .init(t)
    }
  }

  /// Parses a wildcard type literal.
  ///
  ///     wildcard-type-literal ::=
  ///       '_'
  ///
  private mutating func parseWildcardTypeLiteral(
    in file: inout Module.SourceContainer
  ) throws -> WildcardTypeLiteral.ID {
    let u = try take(.underscore) ?? expected("'_'")
    return file.insert(WildcardTypeLiteral(site: u.site))
  }

  /// Parses a type ascription iff the next token is a colon.
  ///
  ///     type-ascription ::=
  ///       ':' expression
  ///
  private mutating func parseOptionalTypeAscription(
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity? {
    if take(.colon) != nil {
      return try parseExpression(in: &file)
    } else {
      return nil
    }
  }

  /// Parses a return type ascription iff the next token is an arrow.
  ///
  ///     return-type-ascription ::=
  ///       '->' expression
  ///
  private mutating func parseOptionalReturnTypeAscription(
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity? {
    if take(.arrow) != nil {
      return try parseExpression(in: &file)
    } else {
      return nil
    }
  }

  /// Parses the type ascription of a parameter iff the next token is a colon.
  private mutating func parseOptionalParameterTypeAscription(
    in file: inout Module.SourceContainer
  ) throws -> RemoteTypeExpression.ID? {
    switch try parseOptionalTypeAscription(in: &file) {
    case nil:
      return nil
    case .some(let b) where file.tag(of: b) == RemoteTypeExpression.self:
      return RemoteTypeExpression.ID(uncheckedFrom: b.erased)
    case .some(let b):
      let s = file[b].site
      let k = Parsed<AccessEffect>(.let, at: .empty(at: s.start))
      return file.insert(RemoteTypeExpression(access: k, projectee: b, site: s))
    }
  }

  // MARK: Patterns

  /// Parses a pattern.
  ///
  ///     pattern ::=
  ///       binding-pattern
  ///       tuple-pattern
  ///       expression
  ///
  private mutating func parsePattern(
    in file: inout Module.SourceContainer
  ) throws -> PatternIdentity {
    switch peek()?.tag {
    case .inout, .let, .set, .sink:
      return try .init(parseBindingPattern(in: &file))
    case .name where isParsingBindingSubpattern:
      return try .init(parseVariableDeclaration(in: &file))
    case .leftParenthesis:
      return try parseTuplePatternOrParenthesizedPattern(in: &file)
    default:
      return try .init(parseExpression(in: &file))
    }
  }

  /// Parses a binding pattern.
  private mutating func parseBindingPattern(
    in file: inout Module.SourceContainer
  ) throws -> BindingPattern.ID {
    let i = try parseBindingIntroducer()

    // Identifiers occurring in binding subpatterns denote variable declarations.
    isParsingBindingSubpattern = true
    defer { isParsingBindingSubpattern = false }

    let p = try parsePattern(in: &file)
    let a = try parseOptionalTypeAscription(in: &file)
    let s = i.site.extended(upTo: position.index)
    return file.insert(BindingPattern(introducer: i, pattern: p, ascription: a, site: s))
  }

  /// Parses the introducer of a binding pattern.
  ///
  ///     binding-introducer ::=
  ///       'sink'? 'let'
  ///       'var'
  ///       'inout'
  ///
  private mutating func parseBindingIntroducer() throws -> Parsed<BindingPattern.Introducer> {
    switch peek()?.tag {
    case .let:
      return Parsed(.let, at: take()!.site)
    case .var:
      return Parsed(.var, at: take()!.site)
    case .inout:
      return Parsed(.inout, at: take()!.site)
    case .sink:
      if take(.let) == nil { report(expected("'let'")) }
      return Parsed(.sinklet, at: take()!.site)
    default:
      throw expected("binding introducer")
    }
  }

  /// Parses a tuple pattern or a parenthesized pattern.
  ///
  ///     tuple-pattern ::=
  ///       '(' tuple-pattern-body? ')'
  ///     tuple-pattern-body ::=
  ///       labeled-pattern (',' labeled-pattern)*
  ///
  private mutating func parseTuplePatternOrParenthesizedPattern(
    in file: inout Module.SourceContainer
  ) throws -> PatternIdentity {
    let start = try peek() ?? expected("'('")
    let (es, lastComma) = try inParentheses { (me) in
      try me.parseLabeledPatternList(in: &file)
    }

    if (es.count == 1) && (es[0].label == nil) && (lastComma == nil) {
      return es[0].value
    } else {
      let t = file.insert(
        TuplePattern(elements: es, site: start.site.extended(upTo: position.index)))
      return .init(t)
    }
  }

  /// Parses a parenthesized list of labeled expressions.
  ///
  ///     labeled-pattern-list ::=
  ///       labeled-pattern (',' labeled-pattern)* ','?
  ///     labeled-pattern ::=
  ///       (expression-label ':')? pattern
  ///
  private mutating func parseLabeledPatternList(
    in file: inout Module.SourceContainer
  ) throws -> ([LabeledPattern], lastComma: Token?) {
    try labeledSyntaxList(delimitedBy: .rightParenthesis) { (me) in
      try me.parsePattern(in: &file)
    }
  }

  // MARK: Statements

  /// Parses a statement.
  ///
  ///     statement ::=
  ///       discard-statement
  ///       return-statement
  ///       declaration
  ///       expression
  ///
  private mutating func parseStatement(
    in file: inout Module.SourceContainer
  ) throws -> StatementIdentity {
    let head = try peek() ?? expected("statement")

    switch head.tag {
    case .underscore:
      return try .init(parseDiscardStement(in: &file))
    case .return:
      return try .init(parseReturnStatement(in: &file))
    case _ where head.isDeclarationHead:
      return try .init(parseDeclaration(in: &file))
    default:
      return try .init(parseExpression(in: &file))
    }
  }

  /// Parses a discard statement.
  ///
  ///     return-statement ::=
  ///       '_' '=' expression
  ///
  private mutating func parseDiscardStement(
    in file: inout Module.SourceContainer
  ) throws -> Discard.ID {
    let i = try take(.underscore) ?? expected("'_'")
    if take(.assign) == nil {
      throw expected("'='")
    }
    let v = try parseExpression(in: &file)
    return file.insert(Discard(value: v, site: span(from: i)))
  }

  /// Parses a return statement.
  ///
  ///     return-statement ::=
  ///       'return' expression?
  ///
  private mutating func parseReturnStatement(
    in file: inout Module.SourceContainer
  ) throws -> Return.ID {
    let i = try take(.return) ?? expected("'return'")

    // The return value must be on the same line.
    let v: ExpressionIdentity?
    if newlinesBeforeNextToken() {
      v = nil
    } else if let w = attempt({ (me) in try me.parseExpression(in: &file) }) {
      v = w
    } else {
      report(missingSemicolon(at: .empty(at: position)))
      v = nil
    }

    return file.insert(Return(introducer: i, value: v, site: span(from: i)))
  }

  private mutating func newlinesBeforeNextToken() -> Bool {
    if let t = peek() {
      return tokens.source[position.index ..< t.site.start.index].contains(where: \.isNewline)
    } else {
      return false
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

  /// Parses an operator identifier.
  ///
  ///     operator-identifier ::= (token)
  ///       operator-notation operator
  ///
  private mutating func parseOperatorIdentifier(
  ) throws -> Parsed<FunctionDeclaration.Identifier> {
    let head = try take(if: \.isOperatorNotation) ?? expected("operator notation")
    let notation: OperatorNotation = switch head.tag {
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

  /// Parses an infix operator and returns the region of the file from which it has been extracted
  /// iff it binds less than or as tightly as `p`.
  private mutating func parseInfixOperator(
    notTighterThan p: PrecedenceGroup
  ) throws -> (SourceSpan, PrecedenceGroup)? {
    let s = tokens.save()
    let l = lookahead

    let o = try parseOperator()
    let q = PrecedenceGroup(containing: o.text)
    if (p < q) || ((p == q) && !q.isRightAssociative) {
      return (o, q)
    } else {
      tokens.restore(s)
      lookahead = l
      return nil
    }
  }

  /// Parses a simple identifier.
  private mutating func parseSimpleIdentifier() -> Parsed<String> {
    if let n = take(.name) {
      return .init(String(n.text), at: n.site)
    } else {
      report(expected("identifier"))
      return .init("$!", at: .empty(at: position))
    }
  }

  // MARK: Helpers

  /// Returns a source span from the first position of `t` to the current position.
  private func span(from t: Token) -> SourceSpan {
    .init(t.site.start.index ..< position.index, in: tokens.source)
  }

  /// Returns a source span from `s` to the current position.
  private func span(from s: SourcePosition) -> SourceSpan {
    .init(s.index ..< position.index, in: tokens.source)
  }

  /// Returns `true` iff there is a whitespace at the current position.
  private func whitespaceAtCurrentPosition() -> Bool {
    tokens.source[position.index].isWhitespace
  }

  /// Returns `true` iff there is a whitespace before the next token.
  private mutating func whitespaceBeforeNextToken() -> Bool {
    if let n = peek() {
      return tokens.source[position.index ..< n.site.start.index].contains(where: \.isWhitespace)
    } else {
      return false
    }
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

  /// Consumes and returns the next token iff it has tag `k`; otherwise, returns `nil`.
  private mutating func take(_ k: Token.Tag) -> Token? {
    peek()?.tag == k ? take() : nil
  }

  /// Consumes and returns the next token iff it satisifies `predicate`; otherwise, returns `nil`.
  private mutating func take(if predicate: (Token) -> Bool) -> Token? {
    if let t = peek(), predicate(t) {
      return take()
    } else {
      return nil
    }
  }

  /// COnsumes and returns the next token iff it is a contextual keyword withe the given value.
  private mutating func take(contextual s: String) -> Token? {
    take(if: { (t) in (t.tag == .name) && (t.text == s) })
  }

  /// Consumes and returns the next token iff its tag is in `ks`; otherwise, returns `nil`.
  private mutating func take<T: Collection<Token.Tag>>(oneOf ks: T) -> Token? {
    take(if: { (t) in ks.contains(t.tag) })
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
      switch t.tag {
      case .leftBrace:
        nesting += 1
      case .rightBrace where nesting <= 0:
        _ = take(); return
      case .rightBrace:
        nesting -= 1
      default:
         break
      }
      _ = take()
    }
  }

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

  /// Parses an instance of `T` with an optional argument label.
  private mutating func labeled<T: LabeledSyntax>(
    _ parse: (inout Self) throws -> T.Value
  ) rethrows -> T {
    var backup = self

    // Can we parse a label?
    if let l = take(if: \.isArgumentLabel) {
      if take(.colon) != nil {
        let v = try parse(&self)
        return .init(label: .init(l), value: v)
      } else {
        swap(&self, &backup)
      }
    }

    // No label
    let v = try parse(&self)
    return .init(label: nil, value: v)
  }

  /// Parses a parenthesized list of labeled syntax.
  private mutating func labeledSyntaxList<T: LabeledSyntax>(
    delimitedBy rightDelimiter: Token.Tag,
    _ parse: (inout Self) throws -> T.Value
  ) throws -> ([T], lastComma: Token?) {
    try commaSeparated(delimitedBy: rightDelimiter) { (me) in
      try me.labeled(parse)
    }
  }

  /// Parses an instance of `T` enclosed in `delimiters`.
  private mutating func between<T>(
    _ delimiters: (left: Token.Tag, right: Token.Tag),
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

  /// Parses an instance of `T` enclosed in angle brackets.
  private mutating func inAngles<T>(_ parse: (inout Self) throws -> T) throws -> T {
    try between((.leftAngle, .rightAngle), parse)
  }

  /// Parses an instance of `T` enclosed in braces.
  private mutating func inBraces<T>(_ parse: (inout Self) throws -> T) throws -> T {
    try between((.leftBrace, .rightBrace), parse)
  }

  /// Parses an instance of `T` enclosed in parentheses.
  private mutating func inParentheses<T>(_ parse: (inout Self) throws -> T) throws -> T {
    try between((.leftParenthesis, .rightParenthesis), parse)
  }

  /// Parses a list of instances of `T` separated by colons.
  private mutating func commaSeparated<T>(
    delimitedBy isRightDelimiter: (Token) -> Bool, _ parse: (inout Self) throws -> T
  ) throws -> ([T], lastComma: Token?) {
    var xs: [T] = []
    var lastComma: Token? = nil
    while let head = peek() {
      if isRightDelimiter(head) { break }
      do {
        try xs.append(parse(&self))
      } catch let e as ParseError {
        report(e)
        recover(at: { (t) in isRightDelimiter(t) || t.tag == .comma })
      }
      if let c = take(.comma) { lastComma = c }
    }
    return (xs, lastComma)
  }

  /// Parses a list of instances of `T` separated by colons.
  private mutating func commaSeparated<T>(
    delimitedBy rightDelimiter: Token.Tag?, _ parse: (inout Self) throws -> T
  ) throws -> ([T], lastComma: Token?) {
    try commaSeparated(delimitedBy: { (t) in t.tag == rightDelimiter }, parse)
  }

  /// Parses a list of instances of `T` separated by semicolons.
  private mutating func semicolonSeparated<T>(
    delimitedBy rightDelimiter: Token.Tag?, _ parse: (inout Self) throws -> T
  ) throws -> [T] {
    var xs: [T] = []
    while let head = peek() {
      discard(while: { $0.tag == .semicolon })
      if head.tag == rightDelimiter { break }
      do {
        try xs.append(parse(&self))
      } catch let e as ParseError {
        report(e)
        recover(at: { (t) in t.tag == rightDelimiter || t.tag == .semicolon })
      }
    }
    return xs
  }

  /// Returns a parse error reporting that `s` was expected at the current position.
  private func expected(_ s: String) -> ParseError {
    expected(s, at: .empty(at: position))
  }

  /// Returns a parse error reporting that `s` was expected at `site`.
  private func expected(_ s: String, at site: SourceSpan) -> ParseError {
    .init("expected \(s)", at: site)
  }

  /// Returns a parse error reporting a missing statement separator at `site`.
  func missingSemicolon(at site: SourceSpan) -> ParseError {
    .init("consecutive statements on the same line must be separated by ';'", at: site)
  }

  /// Returns a parse error reporting an unexpected wildcard at `site`.
  func unexpectedWildcard(at site: SourceSpan) -> ParseError {
    let m = """
    '_' can only appear as a pattern, as a compile-time argument, or on the left-hand side of an \
    assignment
    """
    return .init(m, at:  site)
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

extension Token {

  /// Returns a predicate that holds for a token iff that token's tag is in `ks`.
  fileprivate static func oneOf<T: Collection<Token.Tag>>(_ ks: T) -> (Token) -> Bool {
    { (t) in ks.contains(t.tag) }
  }

}

extension Token.Tag {

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
