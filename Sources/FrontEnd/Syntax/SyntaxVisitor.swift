import Utilities

/// A collection of callbacks for visiting an abstract syntax tree.
///
/// Use this protocol to implement algorithms that traverse all or most nodes of an abstract syntax
/// tree and perform similar operations on each of them. Instances of conforming types are meant to
/// be passed as argument to `Syntax.visit(_:calling:)`.
public protocol SyntaxVisitor {

  /// Called when the node `node`, which is in `program`, is about to be entered; returns `false`
  /// if traversal should skip `node`.
  ///
  /// Use this method to perform actions before a node is being traversed and/or customize how the
  /// tree is traversed. If the method returns `true`, `willEnter` will be called before visiting
  /// each child of `node` and `willExit` will be called when `node` is left. If the method returns
  /// `false`, neither `willEnter` nor `willExit` will be called for `node` and its children.
  mutating func willEnter(_ node: AnySyntaxIdentity, in program: Program) -> Bool

  /// Called when the node `node`, which is in `program`, is about to be left.
  mutating func willExit(_ node: AnySyntaxIdentity, in program: Program)

}

extension SyntaxVisitor {

  public mutating func willEnter(_ node: AnySyntaxIdentity, in program: Program) -> Bool { true }

  public mutating func willExit(_ node: AnySyntaxIdentity, in program: Program) {}

}

extension Program {

  /// Calls `visit(_:calling:)` on the abstract syntax tree of `m`.
  public func visit<T: SyntaxVisitor>(_ m: ModuleIdentity, calling v: inout T) {
    for (i, s) in self[m].sources.values.enumerated() {
      for o in s.syntax.indices {
        let f = Program.SourceFileIdentity(module: m, offset: i)
        visit(AnySyntaxIdentity(file: f, offset: o), calling: &v)
      }
    }
  }

  /// Visits `n` and its children in pre-order, calling back `v` when a node is entered or left.
  public func visit<T: SyntaxVisitor>(_ n: AnySyntaxIdentity, calling v: inout T) {
    if !v.willEnter(n, in: self) { return }
    switch kind(of: n) {
    case AssociatedTypeDeclaration.self:
      traverse(castUnchecked(n, to: AssociatedTypeDeclaration.self), calling: &v)
    case ConformanceDeclaration.self:
      traverse(castUnchecked(n, to: ConformanceDeclaration.self), calling: &v)
    case ExtensionDeclaration.self:
      traverse(castUnchecked(n, to: ExtensionDeclaration.self), calling: &v)
    case FunctionDeclaration.self:
      traverse(castUnchecked(n, to: FunctionDeclaration.self), calling: &v)
    case GenericParameterDeclaration.self:
      break
    case ImportDeclaration.self:
      break
    case ParameterDeclaration.self:
      traverse(castUnchecked(n, to: ParameterDeclaration.self), calling: &v)
    case StructDeclaration.self:
      traverse(castUnchecked(n, to: StructDeclaration.self), calling: &v)
    case TraitDeclaration.self:
      traverse(castUnchecked(n, to: TraitDeclaration.self), calling: &v)
    case TypeAliasDeclaration.self:
      traverse(castUnchecked(n, to: TypeAliasDeclaration.self), calling: &v)

    case BooleanLiteral.self:
      break
    case Call.self:
      traverse(castUnchecked(n, to: Call.self), calling: &v)
    case NameExpression.self:
      traverse(castUnchecked(n, to: NameExpression.self), calling: &v)
    case RemoteTypeExpression.self:
      traverse(castUnchecked(n, to: RemoteTypeExpression.self), calling: &v)
    case TupleLiteral.self:
      traverse(castUnchecked(n, to: TupleLiteral.self), calling: &v)

    case Return.self:
      traverse(castUnchecked(n, to: Return.self), calling: &v)

    default:
      unreachable()
    }
    v.willExit(n, in: self)
  }

  /// Visits `n` and its children in pre-order, calling back `v` when a node is entered or left.
  public func visit<T: SyntaxVisitor, U: SyntaxIdentity>(_ n: U?, calling v: inout T) {
    n.map({ (m) in visit(m.erased, calling: &v) })
  }

  /// Visits `ns` and their children in pre-order, calling back `v` when a node is entered or left.
  public func visit<T: SyntaxVisitor, U: Collection>(
    _ ns: U, calling v: inout T
  ) where U.Element: SyntaxIdentity {
    for n in ns {
      visit(n.erased, calling: &v)
    }
  }

  /// If `n` is present, visits `n` and its children in pre-order, calling back `v` when a node is
  /// entered or left.
  public func visit<T: SyntaxVisitor>(_ n: AnySyntaxIdentity?, calling v: inout T) {
    if let m = n { visit(m, calling: &v) }
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: AssociatedTypeDeclaration.ID, calling v: inout T) {}

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: ConformanceDeclaration.ID, calling v: inout T) {
    visit(self[n].extendee.erased, calling: &v)
    visit(self[n].concept.erased, calling: &v)
    visit(self[n].members, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: ExtensionDeclaration.ID, calling v: inout T) {
    visit(self[n].extendee.erased, calling: &v)
    visit(self[n].members, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: FunctionDeclaration.ID, calling v: inout T) {
    visit(self[n].parameters, calling: &v)
    visit(self[n].output, calling: &v)
    if let b = self[n].body { visit(b, calling: &v) }
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: ParameterDeclaration.ID, calling v: inout T) {
    visit(self[n].ascription.map(AnySyntaxIdentity.init(_:)), calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: StructDeclaration.ID, calling v: inout T) {
    visit(self[n].members, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: TraitDeclaration.ID, calling v: inout T) {
    visit(self[n].members, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: TypeAliasDeclaration.ID, calling v: inout T) {
    visit(self[n].aliasee, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: Call.ID, calling v: inout T) {
    visit(self[n].callee, calling: &v)
    for a in self[n].arguments { visit(a.value, calling: &v) }
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: NameExpression.ID, calling v: inout T) {
    if case .explicit(let e) = self[n].qualification {
      visit(e.erased, calling: &v)
    }
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: RemoteTypeExpression.ID, calling v: inout T) {
    visit(self[n].projectee.erased, calling: &v)
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: TupleLiteral.ID, calling v: inout T) {
    for a in self[n].elements { visit(a.value, calling: &v) }
  }

  /// Visits the children of `n` in pre-order, calling back `v` when a node is entered or left.
  public func traverse<T: SyntaxVisitor>(_ n: Return.ID, calling v: inout T) {
    visit(self[n].value, calling: &v)
  }

}
