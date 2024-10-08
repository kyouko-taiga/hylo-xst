import Archivist
import OrderedCollections
import Utilities

/// A Hylo program.
public struct Program {

  /// The identity of a module in loaded in a program.
  public typealias ModuleIdentity = Int

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

  /// Projects the node identified by `n`.
  public subscript<T: Syntax>(n: T.ID) -> T {
    self[n.rawValue] as! T
  }

  /// Projects the node identified by `n`.
  public subscript<T: SyntaxIdentity>(n: T) -> any Syntax {
    _read { yield self[n.rawValue] }
  }

  /// Projects the node identified by `n`.
  internal subscript(n: RawSyntaxIdentity) -> any Syntax {
    _read { yield modules.values[n.module][n] }
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
    self[n.rawValue.module][n.rawValue.file].syntaxToKind[n.rawValue.node]
  }

  /// Returns `true` iff `n` denotes a declaration.
  public func isDeclaration<T: SyntaxIdentity>(_ n: T) -> Bool {
    kind(of: n).value is any Declaration.Type
  }

  /// Returns `true` iff `n` denotes a scope.
  public func isScope<T: SyntaxIdentity>(_ n: T) -> Bool {
    kind(of: n).value is any Scope.Type
  }

  /// Returns `n` if it identifies a node of type `U`; otherwise, returns `nil`.
  public func cast<T: SyntaxIdentity, U: Syntax>(_ n: T, to: U.Type) -> U.ID? {
    if kind(of: n) == .init(U.self) {
      return .init(rawValue: n.rawValue)
    } else {
      return nil
    }
  }

  /// Returns `n` if it identifies a declaration; otherwise, returns `nil`.
  public func castToDeclaration<T: SyntaxIdentity>(_ n: T) -> DeclarationIdentity? {
    if isDeclaration(n) {
      return .init(rawValue: n.rawValue)
    } else {
      return nil
    }
  }

  /// Returns `n` if it identifies a scope; otherwise, returns `nil`.
  public func castToScope<T: SyntaxIdentity>(_ n: T) -> ScopeIdentity? {
    if isScope(n) {
      return .init(rawValue: n.rawValue)
    } else {
      return nil
    }
  }

  /// Returns the innermost scope containing `n` or `nil` if `n` is a top-level declaration.
  ///
  /// - Requires: The module containing `n` has gone through scoping.
  public func parent<T: SyntaxIdentity>(containing n: T) -> ScopeIdentity? {
    let s = self[n.rawValue.module][n.rawValue.file]
    precondition(s.syntaxToParent.count > n.rawValue.node, "unscoped module")

    let p = s.syntaxToParent[n.rawValue.node]
    if p >= 0 {
      return .init(rawValue: .init(module: n.rawValue.module, file: n.rawValue.file, node: p))
    } else {
      return nil
    }
  }

  /// Returns the innermost scope containing `n` if it's a node of type `U`, or `nil` otherwise.
  public func parent<T: SyntaxIdentity, U: Syntax>(containing n: T, as: U.Type) -> U.ID? {
    parent(containing: n).flatMap({ (m) in cast(m, to: U.self) })
  }

  /// Returns the declarations directly contained in `n`.
  ///
  /// - Requires: The module containing `n` has gone through scoping.
  public func declarations(in n: ScopeIdentity) -> DeclarationSet {
    let s = self[n.rawValue.module][n.rawValue.file]
    return s.scopeToDeclarations[n.rawValue.node] ?? preconditionFailure("unscoped module")
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
      return p.identity(module: m) == n.rawValue.module
    case .kind(let k):
      return p.kind(of: n) == k
    }
  }

}
