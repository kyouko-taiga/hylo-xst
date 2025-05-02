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

  /// A sequence of modifiers prefixing a declaration.
  private typealias DeclarationPrologue = [Parsed<DeclarationModifier>]

  /// Parses a declaration.
  ///
  ///     declaration ::=
  ///       associated-type-declaration
  ///       binding-declaration
  ///       extension-declaration
  ///       function-declaration
  ///       given-declaration
  ///       struct-declaration
  ///       trait-declaration
  ///
  private mutating func parseDeclaration(
    in file: inout Module.SourceContainer
  ) throws -> DeclarationIdentity {
    let prologue = parseDeclarationModifiers()

    guard let head = peek() else { throw expected("declaration") }
    switch head.tag {
    case .inout, .let, .set, .sink, .var:
      return try .init(parseBindingDeclaration(after: prologue, in: &file))
    case .fun:
      return try parseFunctionOrBundleDeclaration(after: prologue, in: &file)
    case .given:
      return try parseGivenDeclaration(after: prologue, in: &file)
    case .extension:
      return try .init(parseExtensionDeclaration(after: prologue, in: &file))
    case .`init`:
      return try .init(parseInitializerDeclaration(after: prologue, in: &file))
    case .struct:
      return try .init(parseStructDeclaration(after: prologue, in: &file))
    case .trait:
      return try .init(parseTraitDeclaration(after: prologue, in: &file))
    case .type:
      return try .init(parseAssociatedTypeDeclaration(after: prologue, in: &file))
    case .typealias:
      return try .init(parseTypeAliasDeclaration(after: prologue, in: &file))
    case .name where head.text == "memberwise":
      return try .init(parseInitializerDeclaration(after: prologue, in: &file))
    default:
      throw expected("declaration", at: .empty(at: head.site.start))
    }
  }

  /// Parses a sequence of declaration modifiers.
  private mutating func parseDeclarationModifiers() -> [Parsed<DeclarationModifier>] {
    var modifiers: [Parsed<DeclarationModifier>] = []
    while let m = parseOptionalDeclarationModifiers() {
      append(m)
    }
    return modifiers

    func append(_ m: Parsed<DeclarationModifier>) {
      for i in 0 ..< modifiers.count {
        if modifiers[i].value == m.value {
          report(.init("duplicate modifier", at: m.site))
          return
        } else if !m.value.canOccurWith(modifiers[i].value) {
          report(.init("'\(m.value)' is incompatible with '\(modifiers[i].value)'", at: m.site))
          return
        } else if !m.value.canOccurAfter(modifiers[i].value) {
          report(.init("'\(m.value)' should occur before '\(modifiers[i].value)'", at: m.site))
          modifiers.insert(m, at: i)
          return
        }
      }
      modifiers.append(m)
    }
  }

  /// Parses a sequence of declaration modifier if the next token denotes one.
  ///
  ///     declaration-modifier ::= (one of)
  ///       static private internal private
  ///
  private mutating func parseOptionalDeclarationModifiers() -> Parsed<DeclarationModifier>? {
    parseExpressibleByTokenTag(DeclarationModifier.self)
  }

  /// Parses an associated type declaration.
  ///
  ///     associated-type-declaration ::=
  ///       'type' identifier
  ///
  private mutating func parseAssociatedTypeDeclaration(
    after prologue: DeclarationPrologue, in file: inout Module.SourceContainer
  ) throws -> AssociatedTypeDeclaration.ID {
    let introducer = try take(.type) ?? expected("'type'")
    let identifier = parseSimpleIdentifier()

    // No modifiers allowed on extensions.
    _ = sanitize(prologue, accepting: { _ in false })

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
    asGiven: Bool = false,
    after prologue: DeclarationPrologue, in file: inout Module.SourceContainer
  ) throws -> BindingDeclaration.ID {
    let b = try parseBindingPattern(in: &file)
    let i = try parseOptionalInitializerExpression(in: &file)

    return file.insert(
      BindingDeclaration(
        modifiers: prologue, isGiven: asGiven, pattern: b, initializer: i,
        site: span(from: file[b].site.start)))
  }

  /// Parses an extension declaration.
  ///
  ///     extension-declaration ::=
  ///       'extension' expression type-body
  ///
  private mutating func parseExtensionDeclaration(
    after prologue: DeclarationPrologue, in file: inout Module.SourceContainer
  ) throws -> ExtensionDeclaration.ID {
    let introducer = try take(.extension) ?? expected("'extension'")
    let staticParameters = try parseOptionalCompileTimeParameters(in: &file)
    let extendee = try parseExpression(in: &file)
    let members = try parseTypeBody(in: &file)

    // No modifiers allowed on extensions.
    _ = sanitize(prologue, accepting: { _ in false })

    return file.insert(
      ExtensionDeclaration(
        introducer: introducer,
        staticParameters: staticParameters,
        extendee: extendee,
        members: members,
        site: span(from: introducer)))
  }

  /// Parses a given binding or a conformance declaration.
  ///
  ///     given-declaration ::=
  ///       'given' binding-declaration
  ///       'given' conformance-declaration
  ///
  private mutating func parseGivenDeclaration(
    after prologue: DeclarationPrologue, in file: inout Module.SourceContainer
  ) throws -> DeclarationIdentity {
    let head = try take(.given) ?? expected("'given'")

    // Is the next token a binding introducer?
    let next = try peek() ?? expected("'declaration'")
    if next.isBindingIntroducer {
      return try .init(parseBindingDeclaration(asGiven: true, after: prologue, in: &file))
    }

    // Expect a conformance declaration.
    else {
      let staticParameters = try parseOptionalCompileTimeParameters(in: &file)
      let conformer = try parseExpression(in: &file)
      _ = try take(.colon) ?? expected("':'")
      let concept = try parseExpression(in: &file)
      let witness = desugaredConformance(of: conformer, to: concept, in: &file)

      let members = try parseTypeBody(in: &file)

      let d = file.insert(
        ConformanceDeclaration(
          introducer: head,
          staticParameters: staticParameters,
          witness: witness,
          members: members,
          site: span(from: head)))
      return .init(d)
    }
  }

  /// Parses a function declaration.
  ///
  ///     function-declaration ::=
  ///       function-declaration-head callable-body?
  ///     function-declaration-head ::=
  ///       'fun' function-identifier parameter-clauses return-type-ascription?
  ///
  private mutating func parseFunctionDeclaration(
    after prologue: DeclarationPrologue, in file: inout Module.SourceContainer
  ) throws -> FunctionDeclaration.ID {
    let head = try take(.fun) ?? expected("'fun'")
    let introducer = Parsed(FunctionDeclaration.Introducer.fun, at: head.site)

    let n = try parseFunctionIdentifier()
    let (s, r) = try parseParameterClauses(in: &file)
    let e = parseOptionalAccessEffect() ?? .init(.let, at: .empty(at: position))
    let o = try parseOptionalReturnTypeAscription(in: &file)
    let b = try parseOptionalCallableBody(in: &file)
    return file.insert(
      FunctionDeclaration(
        modifiers: prologue,
        introducer: introducer, identifier: n,
        staticParameters: s, parameters: r,
        effect: e,
        output: o, body: b,
        site: introducer.site.extended(upTo: position.index)))
  }

  /// Parses a function bundle declaration.
  ///
  ///     function-declaration ::=
  ///       function-head callable-body?
  ///     function-head ::=
  ///       'fun' function-identifier parameter-clauses access-effect? return-type-ascription?
  ///     function-bundle-declaration ::=
  ///       function-bundle-head bundle-body?
  ///     function-bundle-head ::=
  ///       'fun' function-identifier parameter-clauses 'auto' return-type-ascription?
  ///
  private mutating func parseFunctionOrBundleDeclaration(
    after prologue: DeclarationPrologue, in file: inout Module.SourceContainer
  ) throws -> DeclarationIdentity {
    let head = try take(.fun) ?? expected("'fun'")
    let introducer = Parsed(FunctionDeclaration.Introducer.fun, at: head.site)

    let identifier = try parseFunctionIdentifier()
    let (ss, ps) = try parseParameterClauses(in: &file)
    let effect = parseOptionalAccessEffect() ?? .init(.let, at: .empty(at: position))
    let output = try parseOptionalReturnTypeAscription(in: &file)

    if effect.value == .auto {
      let b = try parseBundleBody(in: &file)
      let i = asBundleIdentifier(identifier)
      let n = file.insert(
        FunctionBundleDeclaration(
          modifiers: prologue,
          introducer: .init(head, at: head.site), identifier: i,
          staticParameters: ss, parameters: ps, effect: effect,
          output: output, variants: b,
          site: introducer.site.extended(upTo: position.index)))
      return .init(n)
    } else {
      let b = try parseOptionalCallableBody(in: &file)
      let n = file.insert(
        FunctionDeclaration(
          modifiers: prologue,
          introducer: introducer, identifier: identifier,
          staticParameters: ss, parameters: ps, effect: effect,
          output: output, body: b,
          site: introducer.site.extended(upTo: position.index)))
      return .init(n)
    }
  }

  /// Parses an initializer declaration.
  ///
  ///     initializer-declaration ::=
  ///       'init' parameter-clauses callable-body?
  ///       'memberwise' 'init'
  ///
  private mutating func parseInitializerDeclaration(
    after prologue: DeclarationPrologue, in file: inout Module.SourceContainer
  ) throws -> FunctionDeclaration.ID {
    let introducer = try parseInitializerIntroducer()

    // Custom initializer?
    if introducer.value == .`init` {
      let (s, r) = try parseParameterClauses(in: &file)
      let b = try parseOptionalCallableBody(in: &file)
      return file.insert(
        FunctionDeclaration(
          modifiers: sanitize(prologue, accepting: \.isApplicableToInitializer),
          introducer: introducer, identifier: .init(.simple("init"), at: introducer.site),
          staticParameters: s, parameters: r,
          effect: .init(.set, at: .empty(at: position)),
          output: nil, body: b,
          site: introducer.site.extended(upTo: position.index)))
    }

    // Memberwise initializer?
    else if introducer.value == .memberwiseinit {
      return file.insert(
        FunctionDeclaration(
          modifiers: sanitize(prologue, accepting: \.isApplicableToInitializer),
          introducer: introducer, identifier: .init(.simple("init"), at: introducer.site),
          staticParameters: .empty(at: .empty(at: position)), parameters: [],
          effect: .init(.set, at: .empty(at: position)),
          output: nil, body: nil,
          site: introducer.site))
    }

    else { unreachable("invalid introducer") }
  }

  /// Parses the introducer of an initializer declaration.
  ///
  ///     initializer-introducer ::=
  ///       'memberwise'? 'init'
  ///
  private mutating func parseInitializerIntroducer() throws
    -> Parsed<FunctionDeclaration.Introducer>
  {
    if let t = take(.`init`) {
      return .init(.`init`, at: t.site)
    } else if let t = take(contextual: "memberwise") {
      let u = take(.`init`) ?? fix(expected("'init'"), with: t)
      return .init(.memberwiseinit, at: t.site.extended(toCover: u.site))
    } else {
      throw expected("'init'")
    }
  }

  /// Parses the parameter clauses of a callable declaration.
  ///
  ///     parameter-clauses ::=
  ///       compile-time-parameters? run-time-parameters
  ///
  private mutating func parseParameterClauses(
    in file: inout Module.SourceContainer
  ) throws -> (StaticParameters, [ParameterDeclaration.ID]) {
    let s = try parseOptionalCompileTimeParameters(in: &file)
    let r = try parseParenthesizedParameterList(in: &file)
    return (s, r)
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
    let (ps, _) = try commaSeparated(until: Token.oneOf([.rightAngle, .where])) { (me) in
      try me.parseGenericParameterDeclaration(in: &file)
    }
    return ps
  }

  /// Parses a generic parameter declaration.
  ///
  ///     generic-parameter ::=
  ///       identifier kind-ascription?
  ///
  private mutating func parseGenericParameterDeclaration(
    in file: inout Module.SourceContainer
  ) throws -> GenericParameterDeclaration.ID {
    let n = try take(.name) ?? expected("identifier")
    let a = try parseOptionalKindAscription(in: &file)
    return file.insert(
      GenericParameterDeclaration(identifier: .init(n), ascription: a, site: n.site))
  }

  /// Parses a list of context bounds iff the next token is a colon.
  ///
  ///     context-bound-list ::=
  ///       ':' compound-expression ('&' compound-expression)*
  ///
  private mutating func parseOptionalContextBoundList(
    until rightDelimiter: Token.Tag, in file: inout Module.SourceContainer
  ) throws -> [ConformanceDeclaration.ID] {
    if let introducer = take(.colon) {
      return try ampersandSeparated(until: rightDelimiter) { me in
        try me.parseContextBound(introducedBy: introducer, in: &file)
      }
    } else {
      return []
    }
  }

  /// Parses a context bound.
  ///
  ///     context-bound ::=
  ///       compound-expression
  ///
  /// A context bound is parsed as a compound expression and immediately desugared as a static call
  /// whose first argument is a name expression referring to the conforming type. For example, if
  /// the bound is spelled out as `P<A>` in source, it is desugared as `P<Self, A>`.
  private mutating func parseContextBound(
    introducedBy introducer: Token,
    in file: inout Module.SourceContainer
  ) throws -> ConformanceDeclaration.ID {
    let b = try parseCompoundExpression(in: &file)
    let w = try desugared(bound: b)
    let s = file[w].site

    return file.insert(
      ConformanceDeclaration(
        introducer: introducer, staticParameters: .empty(at: s), witness: w, members: [], site: s))

    /// Desugards a compound expression into a call of the form `P<Self, ...>`.
    func desugared(bound b: ExpressionIdentity) throws -> StaticCall.ID {
      switch file[b] {
      case let n as NameExpression:
        return file.insert(StaticCall(callee: b, arguments: conformer(), site: n.site))
      case let n as StaticCall:
        return file.replace(b, for: n.replacing(arguments: conformer() + n.arguments))
      case let n:
        throw ParseError("invalid context bound", at: n.site)
      }
    }

    /// Returns a name expression referring to the conforming type.
    func conformer() -> [ExpressionIdentity] {
      let s = SourceSpan.empty(at: position)
      let e = file.insert(NameExpression(qualification: nil, name: .init("Self", at: s), site: s))
      return [.init(e)]
    }
  }

  /// Parses a where clause iff the next token is `.where`. Otherwise, returns an empty clause.
  private mutating func parseOptionalWhereClause(
    in file: inout Module.SourceContainer
  ) throws -> [DeclarationIdentity] {
    guard take(.where) != nil else { return [] }
    let (ps, _) = try commaSeparated(until: .rightAngle) { (me) in
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

    let witness: ExpressionIdentity
    if s.tag == .colon {
      witness = .init(desugaredConformance(of: l, to: r, in: &file))
    } else {
      let w = EqualityWitnessExpression(
        lhs: l, rhs: r, site: file[l].site.extended(toCover: file[r].site))
      witness = .init(file.insert(w))
    }

    let d = file.insert(UsingDeclaration(witness: witness, site: file[witness].site))
    return .init(d)
  }

  /// Parses a parenthesized list of parameter declarations.
  private mutating func parseParenthesizedParameterList(
    in file: inout Module.SourceContainer
  ) throws -> [ParameterDeclaration.ID] {
    let (ps, _) = try inParentheses { (m0) in
      try m0.commaSeparated(until: .rightParenthesis) { (m1) in
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

    let ascription = try parseOptionalParameterAscription(in: &file)
    let defaultValue = try parseOptionalInitializerExpression(in: &file)

    return file.insert(
      ParameterDeclaration(
        label: label,
        identifier: identifier,
        ascription: ascription,
        defaultValue: defaultValue,
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
      try m0.semicolonSeparated(until: .rightBrace) { (m1) in
        try m1.parseStatement(in: &file)
      }
    }
  }

  private mutating func parseBundleBody(
    in file: inout Module.SourceContainer
  ) throws -> [VariantDeclaration.ID] {
    let start = position
    let vs = try inBraces { (m0) in
      try m0.semicolonSeparated(until: .rightBrace) { (m1) in
        try m1.parseVariant(in: &file)
      }
    }

    if vs.isEmpty {
      report(.init("bundle requires at least one variant declaration", at: .empty(at: start)))
    }
    return vs
  }

  /// Parses the body of a variant in a function or subscript bundle.
  private mutating func parseVariant(
    in file: inout Module.SourceContainer
  ) throws -> VariantDeclaration.ID {
    let k = try parseOptionalAccessEffect() ?? expected("access effect")
    let b = try parseOptionalCallableBody(in: &file)
    return file.insert(VariantDeclaration(effect: k, body: b, site: span(from: k.site.start)))
  }

  /// Parses a struct declaration.
  ///
  ///     struct-declaration ::=
  ///       'struct' identifier type-body
  ///
  private mutating func parseStructDeclaration(
    after prologue: DeclarationPrologue, in file: inout Module.SourceContainer
  ) throws -> StructDeclaration.ID {
    let introducer = try take(.struct) ?? expected("'struct'")
    let identifier = parseSimpleIdentifier()
    let staticParameters = try parseOptionalCompileTimeParameters(in: &file)
    let contextBounds = try parseOptionalContextBoundList(until: .leftBrace, in: &file)
    let members = try parseTypeBody(in: &file)

    return file.insert(
      StructDeclaration(
        modifiers: sanitize(prologue, accepting: \.isApplicableToTypeDeclaration),
        introducer: introducer,
        identifier: identifier,
        staticParameters: staticParameters,
        contextBounds: contextBounds,
        members: members,
        site: span(from: introducer)))
  }

  /// Parses a trait declaration.
  ///
  ///     trait-declaration ::=
  ///       'trait' identifier type-body
  ///
  private mutating func parseTraitDeclaration(
    after prologue: DeclarationPrologue, in file: inout Module.SourceContainer
  ) throws -> TraitDeclaration.ID {
    let introducer = try take(.trait) ?? expected("'trait'")
    let identifier = parseSimpleIdentifier()
    let parameters = try parseOptionalCompileTimeParameters(in: &file)
    let members = try parseTypeBody(in: &file)

    if let p = parameters.implicit.first {
      report(.init("constraints on trait parameters are not supported yet", at: file[p].site))
    }

    return file.insert(
      TraitDeclaration(
        modifiers: sanitize(prologue, accepting: \.isApplicableToTypeDeclaration),
        introducer: introducer,
        identifier: identifier,
        parameters: parameters.explicit,
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
      try m0.semicolonSeparated(until: .rightBrace) { (m1) in
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
    after prologue: DeclarationPrologue, in file: inout Module.SourceContainer
  ) throws -> TypeAliasDeclaration.ID {
    let introducer = try take(.typealias) ?? expected("'typealias'")
    let identifier = parseSimpleIdentifier()
    _ = try take(.assign) ?? expected("'='")
    let aliasee = try parseExpression(in: &file)

    return file.insert(
      TypeAliasDeclaration(
        modifiers: sanitize(prologue, accepting: \.isApplicableToTypeDeclaration),
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

  /// Parses an initializer/default expression iff the next token an equal sign.
  ///
  ///     initializer-expression ::=
  ///       '=' expression
  ///
  private mutating func parseOptionalInitializerExpression(
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity? {
    if take(.assign) != nil {
      return try parseExpression(in: &file)
    } else {
      return nil
    }
  }

  /// Returns `modifiers` sans those that do not satisfy `isValid`.
  private mutating func sanitize(
    _ modifiers: consuming DeclarationPrologue, accepting isValid: (DeclarationModifier) -> Bool
  ) -> DeclarationPrologue {
    var end = modifiers.count
    for i in (0 ..< modifiers.count).reversed() where !isValid(modifiers[i].value) {
      report(.init("declaration cannot be marked '\(modifiers[i].value)'", at: modifiers[i].site))
      modifiers.swapAt(i, end - 1)
      end -= 1
    }
    return .init(modifiers.prefix(upTo: end))
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
      // Next token isn't considered an infix operator unless it is surrounded by whitespaces.
      guard let h = peek(), h.isOperator, whitespaceBeforeNextToken() else { break }
      guard let (o, q) = try parseOptionalInfixOperator(notTighterThan: p) else { break }

      let r = try parseInfixExpression(minimumPrecedence: q.next, in: &file)
      let f = file.insert(
        NameExpression(
          qualification: l,
          name: .init(Name(identifier: String(o.text), notation: .infix), at: o),
          site: o))
      let n = file.insert(
        Call(
          callee: .init(f),
          arguments: [.init(label: nil, value: r)], style: .parenthesized,
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
    // Is there a prefix operator? (note: `&` is not a prefix operator)
    if let h = peek(), h.isOperator, (h.tag != .ampersand) {
      let o = try parseOperator()
      if whitespaceBeforeNextToken() { report(separatedUnaryOperator(o)) }

      let e = try parseCompoundExpression(in: &file)
      let f = file.insert(
        NameExpression(
          qualification: e,
          name: .init(Name(identifier: String(o.text), notation: .prefix), at: o),
          site: o))
      let n = file.insert(
        Call(
          callee: .init(f),
          arguments: [], style: .parenthesized,
          site: span(from: file[e].site.start)))
      return .init(n)
    }

    // No prefix operator; simply parse a compound expression.
    else { return try parseCompoundExpression(in: &file) }
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
    // Is there a mutation marker?
    var marker = take(.ampersand)
    if let m = marker, whitespaceBeforeNextToken() {
      report(separatedUnaryOperator(m.site))
    }

    var head = try parsePrimaryExpression(in: &file)

    while true {
      // The period separating nominal components binds more tightly than mutation markers.
      if try appendNominalComponent(to: &head, in: &file) {
        continue
      } else if let m = marker.take() {
        head = .init(file.insert(InoutExpression(marker: m, lvalue: head, site: span(from: m))))
      }

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
    let n = try parseName()
    let s = span(from: file[h].site.start)
    let m = file.insert(NameExpression(qualification: h, name: n, site: s))
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
      try me.parseLabeledExpressionList(until: .rightParenthesis, in: &file)
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
      try m0.commaSeparated(until: .rightAngle) { (m1) in
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
    until rightDelimiter: Token.Tag,
    in file: inout Module.SourceContainer
  ) throws -> ([LabeledExpression], lastComma: Token?) {
    try labeledSyntaxList(until: rightDelimiter) { (me) in
      try me.parseExpression(in: &file)
    }
  }

  /// Parses a primary expression.
  ///
  ///     primary-expression ::=
  ///       boolean-literal
  ///       tuple-literal
  ///       wildcard-literal
  ///       unqualified-name-expression
  ///       impliclty-qualified-name-expression
  ///       remote-type-expression
  ///       singleton-type-expression
  ///       tuple-type-expression
  ///       '(' expression ')'
  ///
  private mutating func parsePrimaryExpression(
    in file: inout Module.SourceContainer
  ) throws -> ExpressionIdentity {
    switch peek()?.tag {
    case .true, .false:
      return .init(file.insert(BooleanLiteral(site: take()!.site)))
    case .underscore:
      return try .init(parseWildcardLiteral(in: &file))
    case .dot:
      return try .init(parseImplicitlyQualifiedNameExpression(in: &file))
    case .name:
      return try .init(parseUnqualifiedNameExpression(in: &file))
    case .auto, .inout, .let, .set, .sink:
      return try .init(parseRemoteTypeExpression(in: &file))
    case .leftBrace:
      return try .init(parseTupleTypeExpression(in: &file))
    case .leftParenthesis:
      return try parseTupleLiteralOrParenthesizedExpression(in: &file)
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
  ///       auto let inout set sink
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
    parseExpressibleByTokenTag(AccessEffect.self)
  }

  /// Parses a name expression with an implicit qualification.
  ///
  ///     implicitly-qualified-name-expression ::=
  ///       '.' identifier
  ///
  private mutating func parseImplicitlyQualifiedNameExpression(
    in file: inout Module.SourceContainer
  ) throws -> NameExpression.ID {
    let dot = try take(.dot) ?? expected("'.'")
    let n = try parseName()
    let q = file.insert(ImplicitQualification(site: dot.site))
    return file.insert(NameExpression(qualification: .init(q), name: n, site: span(from: dot)))
  }

  /// Parses an unqualified name expression.
  ///
  ///     unqualified-name-expression ::= (token)
  ///       identifier ('@' access-effect)?
  ///
  private mutating func parseUnqualifiedNameExpression(
    in file: inout Module.SourceContainer
  ) throws -> NameExpression.ID {
    let n = try parseName()
    return file.insert(NameExpression(qualification: .none, name: n, site: n.site))
  }

  /// Parses a name.
  private mutating func parseName() throws -> Parsed<Name> {
    let head = try peek() ?? expected("name")

    var identifier: String
    var notation: OperatorNotation = .none
    var introducer: AccessEffect? = nil

    if head.isOperatorNotation {
      (notation, identifier) = try parseOperatorIdentifier().value
    } else if head.tag == .name {
      _ = take()
      identifier = String(head.text)
    } else {
      throw expected("name")
    }

    if take(affixed: .at) != nil {
      introducer = parseAccessEffect().value
    }

    return .init(
      Name(identifier: identifier, notation: notation, introducer: introducer),
      at: span(from: head.site.start))
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
      try me.parseLabeledExpressionList(until: .rightBrace, in: &file)
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
      try me.parseLabeledExpressionList(until: .rightParenthesis, in: &file)
    }

    if (elements.count == 1) && (elements[0].label == nil) && (lastComma == nil) {
      return elements[0].value
    } else {
      let t = file.insert(
        TupleLiteral(elements: elements, site: start.site.extended(upTo: position.index)))
      return .init(t)
    }
  }

  /// Parses a wildcard literal.
  ///
  ///     wildcard-literal ::=
  ///       '_'
  ///
  private mutating func parseWildcardLiteral(
    in file: inout Module.SourceContainer
  ) throws -> WildcardLiteral.ID {
    let u = try take(.underscore) ?? expected("'_'")
    return file.insert(WildcardLiteral(site: u.site))
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

  /// Parses a kind ascription iff the next token is a double colon.
  ///
  ///     kind-ascription ::=
  ///       '::' kind-expression
  ///
  private mutating func parseOptionalKindAscription(
    in file: inout Module.SourceContainer
  ) throws -> KindExpression.ID? {
    if take(.doubleColon) != nil {
      return try parseKind(in: &file)
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
  private mutating func parseOptionalParameterAscription(
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

  // MARK: Kinds

  /// Parses a the expression of a kind.
  ///
  ///     kind-expression ::=
  ///       '*'
  ///       '(' kind-expression ')'
  ///       kind-expression ('->' kind-expression)*
  ///
  private mutating func parseKind(
    in file: inout Module.SourceContainer
  ) throws -> KindExpression.ID {
    if peek()?.tag == .leftParenthesis {
      return try inParentheses({ (me) in try me.parseKind(in: &file) })
    }

    let head = try take(.star) ?? expected("kind")
    var kind = file.insert(KindExpression(value: .proper, site: head.site))

    while take(.arrow) != nil {
      let r = try parseKind(in: &file)
      let s = head.site.extended(upTo: position.index)
      kind = file.insert(KindExpression(value: .arrow(kind, r), site: s))
    }

    return kind
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
    case .underscore:
      return try .init(parseWildcardLiteral(in: &file))
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
    case .set:
      return Parsed(.set, at: take()!.site)
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
    try labeledSyntaxList(until: .rightParenthesis) { (me) in
      try me.parsePattern(in: &file)
    }
  }

  // MARK: Statements

  /// Parses a statement.
  ///
  ///     statement ::=
  ///       assignment-statement
  ///       discard-statement
  ///       return-statement
  ///       declaration
  ///       expression
  ///
  private mutating func parseStatement(
    in file: inout Module.SourceContainer
  ) throws -> StatementIdentity {
    let head = try peek() ?? expected("statement")
    defer { ensureStatementDelimiter() }

    switch head.tag {
    case .underscore:
      return try .init(parseDiscardStement(in: &file))
    case .return:
      return try .init(parseReturnStatement(in: &file))
    case _ where head.isDeclarationHead:
      return try .init(parseDeclaration(in: &file))
    default:
      return try parseAssignmentOrExpression(in: &file)
    }
  }

  /// Parses a discard statement.
  ///
  ///     discard-statement ::=
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
    if statementDelimiterBeforeNextToken() {
      v = nil
    } else if let w = attempt({ (me) in try me.parseExpression(in: &file) }) {
      v = w
    } else {
      report(missingSemicolon(at: .empty(at: position)))
      v = nil
    }

    return file.insert(Return(introducer: i, value: v, site: span(from: i)))
  }

  /// Parses an assignment or an expression.
  ///
  ///     assignment-statement ::=
  ///       expression '=' expression
  ///
  private mutating func parseAssignmentOrExpression(
    in file: inout Module.SourceContainer
  ) throws -> StatementIdentity {
    let l = try parseExpression(in: &file)
    if let a = take(.assign) {
      if !withespacesAround(a.site) { report(inconsistentWhitespaces(around: a.site)) }
      let r = try parseExpression(in: &file)
      let n = file.insert(
        Assignment(lhs: l, rhs: r, site: file[l].site.extended(upTo: position.index)))
      return .init(n)
    } else {
      return .init(l)
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
  ) throws -> Parsed<FunctionIdentifier> {
    if let t = peek() {
      if t.isOperatorNotation {
        let i = try parseOperatorIdentifier()
        return .init(.operator(i.value.notation, i.value.identifier), at: i.site)
      } else if t.isOperator {
        report(.init("missing operator notation", at: .empty(at: t.site.start)))
        let o = try parseOperator()
        return .init(.operator(.none, String(o.text)), at: o)
      }
    }

    let identifier = parseSimpleIdentifier()
    return .init(.simple(identifier.value), at: identifier.site)
  }

  /// Returns `i` asa bundle identifier, reporting an error if it's an operator.
  private mutating func asBundleIdentifier(_ i: Parsed<FunctionIdentifier>) -> Parsed<String> {
    if case .simple(let s) = i.value {
      return .init(s, at: i.site)
    } else {
      report(.init("operator identifier cannot be used to name bundle", at: i.site))
      return .init(i.value.description, at: i.site)
    }
  }

  /// Parses an operator identifier.
  ///
  ///     operator-identifier ::= (token)
  ///       operator-notation operator
  ///
  private mutating func parseOperatorIdentifier(
  ) throws -> Parsed<(notation: OperatorNotation, identifier: String)> {
    let n = try parseOperatorNotation()
    let i = try parseOperator()

    if n.site.end != i.start {
      report(.init("illegal space between after operator notation", at: i))
    }

    return .init((n.value, String(i.text)), at: n.site.extended(toCover: i))
  }

  /// Parses an operator notation.
  private mutating func parseOperatorNotation() throws -> Parsed<OperatorNotation> {
    try parseExpressibleByTokenTag(OperatorNotation.self) ?? expected("operator notation")
  }

  /// Parses an operator and returns the region of the file from which it has been extracted.
  private mutating func parseOperator() throws -> SourceSpan {
    // Single-token operators.
    if let t = take(oneOf: [.ampersand, .equal, .operator]) {
      return t.site
    }

    // Multi-token operators.
    let first = try take(oneOf: [.leftAngle, .rightAngle, .star]) ?? expected("operator")
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
  private mutating func parseOptionalInfixOperator(
    notTighterThan p: PrecedenceGroup
  ) throws -> (SourceSpan, PrecedenceGroup)? {
    var backup = self
    let o = try parseOperator()
    let q = PrecedenceGroup(containing: o.text)
    if whitespaceBeforeNextToken() && ((p < q) || ((p == q) && !q.isRightAssociative)) {
      return (o, q)
    } else {
      swap(&self, &backup)
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

  /// Parses an instance of `T` if it can be constructed from the next token.
  private mutating func parseExpressibleByTokenTag<T: ExpressibleByTokenTag>(
    _: T.Type
  ) -> Parsed<T>? {
    if let h = peek(), let v = T(tag: h.tag) {
      _ = take()
      return .init(v, at: h.site)
    } else {
      return nil
    }
  }

  // MARK: Desugarings

  /// Returns the desugaring of a sugared conformance type.
  ///
  /// A sugared conformance type is parsed as `expression ':' expression`. If the RHS is a static
  /// call, this method modifies it in-place to add the LHS as its first argument. Otherwise, a new
  /// static call is created to apply the RHS on the LHS.
  private func desugaredConformance(
    of conformer: ExpressionIdentity, to concept: ExpressionIdentity,
    in file: inout Module.SourceContainer
  ) -> StaticCall.ID {
    let witnessSite = file[conformer].site.extended(toCover: file[concept].site)
    if let rhs = file[concept] as? StaticCall {
      let desugared = StaticCall(
        callee: rhs.callee, arguments: [conformer] + rhs.arguments,
        site: witnessSite)
      return file.replace(concept, for: desugared)
    } else {
      return file.insert(
        StaticCall(callee: concept, arguments: [conformer], site: witnessSite))
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

  /// Returns `true` iff there are whitespaces immediately before and after `s`.
  private func withespacesAround(_ s: SourceSpan) -> Bool {
    let text = tokens.source

    if (s.start.index != text.startIndex) && (s.end.index != text.endIndex) {
      let before = text.index(before: s.start.index)
      return text[before].isWhitespace && text[s.end.index].isWhitespace
    } else {
      return false
    }
  }

  /// Returns `true` iff there is a whitespace before the next token.
  private mutating func whitespaceBeforeNextToken() -> Bool {
    if let n = peek() {
      return tokens.source[position.index ..< n.site.start.index].contains(where: \.isWhitespace)
    } else {
      return false
    }
  }

  /// Returns `true` iff there is a newline before the next token or the character stream is empty.
  private mutating func newlinesBeforeNextToken() -> Bool {
    if let n = peek() {
      return tokens.source[position.index ..< n.site.start.index].contains(where: \.isNewline)
    } else {
      return tokens.source.index(after: position.index) == tokens.source.endIndex
    }
  }

  /// Returns `true` iff there is a statement delimiter before the next token.
  private mutating func statementDelimiterBeforeNextToken() -> Bool {
    (newlinesBeforeNextToken() || next(is: .semicolon) || next(is: .rightBrace))
  }

  /// Returns `true` iff the next token has tag `k`, without consuming that token.
  private mutating func next(is k: Token.Tag) -> Bool {
    peek()?.tag == k
  }

  /// Returns `true` iff the next token satisfies `predicate`, without consuming that token.
  private mutating func next(satisfies predicate: (Token) -> Bool) -> Bool {
    peek().map(predicate) ?? false
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

  /// Consumes and returns the next token iff it has tag `k`.
  private mutating func take(_ k: Token.Tag) -> Token? {
    next(is: k) ? take() : nil
  }

  /// Consumes and returns the next token iff it has tag `k` and no leading whitespace.
  private mutating func take(affixed k: Token.Tag) -> Token? {
    (next(is: k) && !whitespaceBeforeNextToken()) ? take() : nil
  }

  /// Consumes and returns the next token iff it satisifies `predicate`.
  private mutating func take(if predicate: (Token) -> Bool) -> Token? {
    next(satisfies: predicate) ? take() : nil
  }

  /// Consumes and returns the next token iff it is a contextual keyword withe the given value.
  private mutating func take(contextual s: String) -> Token? {
    take(if: { (t) in (t.tag == .name) && (t.text == s) })
  }

  /// Consumes and returns the next token iff its tag is in `ks`.
  private mutating func take<T: Collection<Token.Tag>>(oneOf ks: T) -> Token? {
    take(if: { (t) in ks.contains(t.tag) })
  }

  /// Discards tokens until `predicate` isn't satisfied or all the input has been consumed.
  private mutating func discard(while predicate: (Token) -> Bool) {
    while next(satisfies: predicate) { _ = take() }
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
    attemptOptional({ (me) in try? parse(&me) })
  }

  /// Parses an instance of `T` or restores `self` to its current state if that fails.
  private mutating func attemptOptional<T>(_ parse: (inout Self) -> T?) -> T? {
    var backup = self
    if let result = parse(&self) {
      return result
    } else {
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
    until rightDelimiter: Token.Tag,
    _ parse: (inout Self) throws -> T.Value
  ) throws -> ([T], lastComma: Token?) {
    try commaSeparated(until: rightDelimiter) { (me) in
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
    until isRightDelimiter: (Token) -> Bool, _ parse: (inout Self) throws -> T
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
    until rightDelimiter: Token.Tag?, _ parse: (inout Self) throws -> T
  ) throws -> ([T], lastComma: Token?) {
    try commaSeparated(until: { (t) in t.tag == rightDelimiter }, parse)
  }

  /// Parses a list of instances of `T` separated by newlines or semicolons.
  private mutating func semicolonSeparated<T>(
    until rightDelimiter: Token.Tag?, _ parse: (inout Self) throws -> T
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

  /// Parses a list of instances of `T` separated by ampersands (i.e., `&`).
  private mutating func ampersandSeparated<T>(
    until rightDelimiter: Token.Tag, _ parse: (inout Self) throws -> T
  ) throws -> [T] {
    var xs: [T] = []
    while let head = peek() {
      if head.tag == rightDelimiter { break }
      do {
        try xs.append(parse(&self))
      } catch let e as ParseError {
        report(e)
        recover(at: Token.oneOf([rightDelimiter, .ampersand]))
      }
      _ = take(.ampersand)
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

  /// Ensures there is a statement delimiter before the next token, reporting an error otherwise.
  private mutating func ensureStatementDelimiter() {
    if !statementDelimiterBeforeNextToken() {
      report(missingSemicolon(at: .empty(at: position)))
    }
  }

  /// Returns a parse error reporting a missing statement separator at `site`.
  private func missingSemicolon(at site: SourceSpan) -> ParseError {
    .init("consecutive statements on the same line must be separated by ';'", at: site)
  }

  /// Returns a parse error reporting an unexpected wildcard at `site`.
  private func unexpectedWildcard(at site: SourceSpan) -> ParseError {
    let m = """
    '_' can only appear as a pattern, as a compile-time argument, or on the left-hand side of an \
    assignment
    """
    return .init(m, at:  site)
  }

  /// Returns a parse error reporting inconsistent whitespaces surrounding an infix operator.
  private func inconsistentWhitespaces(around o: SourceSpan) -> ParseError {
    .init("infix operator '\(o.text)' requires whitespaces on both sides", at: o)
  }

  /// Returns a parse error reporting an unary operator separated from its operand.
  private func separatedUnaryOperator(_ o: SourceSpan) -> ParseError {
    .init("unary operator '\(o.text)' cannot be separated from its operand", at: o)
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
public struct ParseError: Error, CustomStringConvertible, Sendable {

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

extension AccessEffect: ExpressibleByTokenTag {

  internal init?(tag: Token.Tag) {
    switch tag {
    case .auto: self = .auto
    case .inout: self = .inout
    case .let: self = .let
    case .set: self = .set
    case .sink: self = .sink
    default: return nil
    }
  }

}

extension DeclarationModifier: ExpressibleByTokenTag {

  internal init?(tag: Token.Tag) {
    switch tag {
    case .static: self = .static
    case .private: self = .private
    case .internal: self = .internal
    case .public: self = .public
    default: return nil
    }
  }

}

extension OperatorNotation: ExpressibleByTokenTag {

  internal init?(tag: Token.Tag) {
    switch tag {
    case .infix: self = .infix
    case .postfix: self = .postfix
    case .prefix: self = .prefix
    default: return nil
    }
  }

}
