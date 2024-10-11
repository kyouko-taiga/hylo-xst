import Archivist
import OrderedCollections
import Utilities

/// A Hylo program.
public struct Program {

  /// The identity of a module in loaded in a program.
  public typealias ModuleIdentity = Int

  /// The identity of a file added to a module.
  public struct SourceFileIdentity: Hashable, RawRepresentable {

    /// The raw value of this identity.
    public let rawValue: UInt32

    /// Creates an instance from its raw value.
    public init(rawValue: UInt32) {
      self.rawValue = rawValue
    }

    /// Creates an instance identifying the file at offset `f` in module `m`.
    public init(module m: Program.ModuleIdentity, offset f: Int) {
      precondition(m < (1 << 16))
      precondition(f < (1 << 16))
      self.rawValue = UInt32(m & 0xffff) + (UInt32(f & 0xffff) << 16)
    }

    /// Creates an instance identifying the file containing `n`.
    public init<T: SyntaxIdentity>(containing n: T) {
      self.rawValue = UInt32(truncatingIfNeeded: n.erased.bits)
    }

    /// The module offset of the node represented by `self` in its containing collection.
    public var module: Program.ModuleIdentity {
      .init(rawValue & 0xffff)
    }

    /// The file offset of the node represented by `self` in its containing collection.
    public var offset: Int {
      .init((rawValue & 0xffff0000) >> 16)
    }

  }

  /// The modules loaded in this program.
  public private(set) var modules = OrderedDictionary<Module.Name, Module>()

  /// The types in the program.
  public internal(set) var types = TypeStore()

  /// Creates an empty program.
  public init() {}

  /// `true` if the program has errors.
  public var containsError: Bool {
    modules.values.contains(where: \.diagnostics.containsError)
  }

  /// The diagnostics of the issues in the program.
  public var diagnostics: some Collection<Diagnostic> {
    modules.values.map(\.diagnostics.elements).joined()
  }

  /// Returns the identities of the modules in `self`.
  public var moduleIdentities: Range<Int> {
    modules.values.indices
  }

  /// Returns the identity of the module named `moduleName`.
  public mutating func demandIdentity(module moduleName: Module.Name) -> ModuleIdentity {
    if let m = modules.index(forKey: moduleName) {
      return m
    } else {
      let m = modules.count
      modules[moduleName] = Module(name: moduleName, identity: m)
      return m
    }
  }

  /// Returns the identity of the module named `moduleName` or `nil` if no such module exists.
  public func identity(module moduleName: Module.Name) -> ModuleIdentity? {
    modules.index(forKey: moduleName)
  }

  /// Computes the scoping relationships in `m`.
  public mutating func assignScopes(_ m: ModuleIdentity) async {
    await Scoper().visit(m, in: &self)
  }

  /// Assigns types to the syntax trees of `m`.
  public mutating func assignTypes(_ m: ModuleIdentity) {
    var typer = Typer(typing: m, in: consume self)
    typer.apply()
    self = typer.release()
  }

  /// Projects the module identified by `m`.
  public subscript(m: ModuleIdentity) -> Module {
    _read { yield modules.values[m] }
    _modify { yield &modules.values[m] }
  }

  /// Projects the source file identified by `f`.
  internal subscript(f: Program.SourceFileIdentity) -> Module.SourceContainer {
    _read { yield modules.values[f.module][f] }
    _modify { yield &modules.values[f.module][f] }
  }

  /// Projects the node identified by `n`.
  public subscript<T: SyntaxIdentity>(n: T) -> any Syntax {
    _read { yield modules.values[n.module][n] }
  }

  /// Projects the node identified by `n`.
  public subscript<T: Syntax>(n: T.ID) -> T {
    modules.values[n.module][n]
  }

  /// Returns a parsable representation of `n`.
  public func show<T: SyntaxIdentity>(_ n: T) -> String {
    self[n].show(readingChildrenFrom: self)
  }

  /// Returns a parsable representation of `t`.
  public func show<T: TypeIdentity>(_ t: T) -> String {
    types[t].show(readingChildrenFrom: self)
  }

  /// Returns the kind of `n`.
  public func kind<T: SyntaxIdentity>(of n: T) -> SyntaxKind {
    modules.values[n.module].kind(of: n)
  }

  /// Returns `true` iff `n` denotes a declaration.
  public func isDeclaration<T: SyntaxIdentity>(_ n: T) -> Bool {
    kind(of: n).value is any Declaration.Type
  }

  /// Returns `true` iff `n` denotes a type declaration.
  public func isTypeDeclaration<T: SyntaxIdentity>(_ n: T) -> Bool {
    kind(of: n).value is any TypeDeclaration.Type
  }

  /// Returns `true` iff `n` introduces a name that can be overloaded.
  public func isOverloadable<T: SyntaxIdentity>(_ n: T) -> Bool {
    switch kind(of: n) {
    case FunctionDeclaration.self:
      return true
    default:
      return false
    }
  }

  /// Returns `true` iff `n` denotes a scope.
  public func isScope<T: SyntaxIdentity>(_ n: T) -> Bool {
    kind(of: n).value is any Scope.Type
  }

  /// Returns `n` if it identifies a node of type `U`; otherwise, returns `nil`.
  public func cast<T: SyntaxIdentity, U: Syntax>(_ n: T, to: U.Type) -> U.ID? {
    if kind(of: n) == .init(U.self) {
      return .init(fromErased: n.erased)
    } else {
      return nil
    }
  }

  /// Returns `n` assuming it identifies a node of type `U`.
  public func castUnchecked<T: SyntaxIdentity, U: Syntax>(_ n: T, to: U.Type = U.self) -> U.ID {
    assert(kind(of: n) == .init(U.self))
    return .init(fromErased: n.erased)
  }

  /// Returns `n` if it identifies a declaration; otherwise, returns `nil`.
  public func castToDeclaration<T: SyntaxIdentity>(_ n: T) -> DeclarationIdentity? {
    if isDeclaration(n) {
      return .init(fromErased: n.erased)
    } else {
      return nil
    }
  }

  /// Returns `n` if it identifies a scope; otherwise, returns `nil`.
  public func castToScope<T: SyntaxIdentity>(_ n: T) -> ScopeIdentity? {
    if isScope(n) {
      return .init(fromErased: n.erased)
    } else {
      return nil
    }
  }

  /// If `n` is not a top-level declaration, returns the innermost scope that contains `n`.
  /// Otherwise, returns `nil`.
  ///
  /// - Requires: The module containing `n` is scoped.
  public func parent<T: SyntaxIdentity>(containing n: T) -> ScopeIdentity? {
    let s = self[n.file]
    precondition(s.syntaxToParent.count > n.offset, "unscoped module")

    let p = s.syntaxToParent[n.offset]
    if p >= 0 {
      return .init(fromErased: .init(file: n.file, offset: p))
    } else {
      return nil
    }
  }

  /// If `n` is not a top-level declaration, returns the innermost scope that contains `n` iff it
  /// is an instance of `U`. Otherwise, returns `nil`.
  ///
  /// - Requires: The module containing `n` is scoped.
  public func parent<T: SyntaxIdentity, U: Syntax>(containing n: T, as: U.Type) -> U.ID? {
    parent(containing: n).flatMap({ (m) in cast(m, to: U.self) })
  }

  /// Returns a sequence containing `s` and its ancestors, from inner to outer.
  ///
  /// - Requires: The module containing `s` is scoped.
  public func scopes(from s: ScopeIdentity) -> any Sequence<ScopeIdentity> {
    var next: Optional = s
    return AnyIterator {
      if let n = next {
        next = parent(containing: n)
        return n
      } else {
        return nil
      }
    }
  }

  /// Returns the declarations directly contained in `n`.
  ///
  /// - Requires: The module containing `n` is scoped.
  public func declarations(in n: ScopeIdentity) -> [DeclarationIdentity] {
    let s = self[n.file]
    return s.scopeToDeclarations[n.offset] ?? preconditionFailure("unscoped module")
  }

  /// Returns the names introduced by `d`.
  public func names(introducedBy d: DeclarationIdentity) -> [Name] {
    switch kind(of: d) {
    case AssociatedTypeDeclaration.self:
      return [name(of: castUnchecked(d, to: AssociatedTypeDeclaration.self))]
    case ClassDeclaration.self:
      return [name(of: castUnchecked(d, to: ClassDeclaration.self))]
    case TraitDeclaration.self:
      return [name(of: castUnchecked(d, to: TraitDeclaration.self))]
    case FunctionDeclaration.self:
      return [name(of: castUnchecked(d, to: FunctionDeclaration.self))]
    default:
      return []
    }
  }

  /// Returns the name of `d`.
  public func name<T: TypeDeclaration>(of d: T.ID) -> Name {
    Name(identifier: self[d].identifier.value)
  }

  /// Returns the name of `d`.
  public func name(of d: FunctionDeclaration.ID) -> Name {
    switch self[d].identifier.value {
    case .simple(let x):
      return Name(identifier: x, labels: .init(self[d].parameters.map(read(\.label?.value))))
    case .operator(let n, let x):
      return Name(identifier: x, notation: n)
    }
  }

  /// Returns `(suffix: s, prefix: p)` where `s` contains the nominal components of `n` from right
  /// to left and `p` is the non-nominal prefix of `n`, if any.
  public func components(
    of n: NameExpression.ID
  ) -> (suffix: [NameExpression.ID], prefix: NameExpression.Qualification) {
    var suffix = [n]
    while true {
      let prefix = self[suffix.last!].qualification
      if case .explicit(let e) = prefix, let m = cast(e, to: NameExpression.self) {
        suffix.append(m)
      } else {
        return (suffix, prefix)
      }
    }
  }

  /// Returns a lambda accessing `path` on an instance of `T`.
  public func read<T: Syntax, U>(_ path: KeyPath<T, U>) -> (_ n: T.ID) -> U {
    { (n) in self[n][keyPath: path] }
  }

  /// Reports that `n` was not expected in the current executation path and exits the program.
  public func unexpected<T: SyntaxIdentity>(
    _ n: T, file: StaticString = #file, line: UInt = #line
  ) -> Never {
    unreachable("unexpected node '\(kind(of: n))' at \(self[n].site)", file: file, line: line)
  }

}

extension Program {

  internal typealias ModuleIdentityMap = [Module.Name: ModuleIdentity]

  /// Serializes `m` to `archive`.
  public func write<A>(module m: ModuleIdentity, to archive: inout WriteableArchive<A>) throws {
    var context: Any = ModuleIdentityMap(
      uniqueKeysWithValues: modules.values.map({ (m) in (m.name, m.identity) }))
    try self[m].write(to: &archive, in: &context)
  }

  /// Serializes `m`.
  public func archive(module m: ModuleIdentity) throws -> BinaryBuffer {
    var w = WriteableArchive(BinaryBuffer())
    try write(module: m, to: &w)
    return w.finalize()
  }

  /// Loads the module named `moduleName` from `archive`.
  ///
  /// - Note: `self` is not modified if an exception is thrown.
  /// - Requires: `moduleName` is the name of the module stored in `archive`.
  @discardableResult
  public mutating func load<A>(
    module moduleName: Module.Name, from archive: inout ReadableArchive<A>
  ) throws -> (loaded: Bool, identity: ModuleIdentity) {
    // Nothing to do if the module is already loaded.
    if let m = modules.index(forKey: moduleName) { return (false, m) }

    let m = modules.count
    var c: ModuleIdentityMap = [moduleName: m]
    for n in modules.values { c[n.name] = n.identity }

    var context: Any = c
    let instance = try archive.read(Module.self, in: &context)
    precondition(moduleName == instance.name)
    modules[moduleName] = instance
    return (true, m)
  }

  /// Loads the module named `moduleName` from `archive`.
  ///
  /// - Note: `self` is not modified if an exception is thrown.
  /// - Requires: `moduleName` is the name of the module stored in `archive`.
  @discardableResult
  public mutating func load(
    module moduleName: Module.Name, from archive: BinaryBuffer
  ) throws -> (loaded: Bool, identity: ModuleIdentity) {
    var r = ReadableArchive(archive)
    return try load(module: moduleName, from: &r)
  }

}

extension Program {

  public func select(_ filter: SyntaxFilter) -> some Collection<AnySyntaxIdentity> {
    modules.values
      .map(\.syntax).joined().lazy
      .filter({ (i) in filter(i, in: self) })
  }

}

/// A selector identifying nodes in a syntax tree.
public indirect enum SyntaxFilter {

  /// Matches any node.
  case all

  /// Matches any node in the given module.
  case from(Module.Name)

  /// Matches any node with the given kind.
  case kind(any Syntax.Type)

  /// Returns `true` if the node `n` of program `p` satisfies `self`.
  public func callAsFunction(_ n: AnySyntaxIdentity, in p: Program) -> Bool {
    switch self {
    case .all:
      return true
    case .from(let m):
      return p.identity(module: m) == n.module
    case .kind(let k):
      return p.kind(of: n) == k
    }
  }

}
