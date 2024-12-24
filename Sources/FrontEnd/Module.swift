import Archivist
import OrderedCollections
import Utilities

/// A collection of declarations in one or more source files.
public struct Module {

  /// The name of a module.
  public typealias Name = String

  /// A source file added to a module.
  internal struct SourceContainer {

    /// The position of `self` in the containing module.
    internal let identity: Program.SourceFileIdentity

    /// The source file contained in `self`.
    internal let source: SourceFile

    /// The abstract syntax of `source`'s contents.
    internal var syntax: [AnySyntax] = []

    /// The top-level declarations in `self`.
    internal var topLevelDeclarations: [DeclarationIdentity] = []

    /// A table from syntax tree to its kind.
    internal var syntaxToKind: [SyntaxKind] = []

    /// A table from syntax tree to the scope that contains it.
    ///
    /// The keys and values of the table are the offsets of the syntax trees in the source file
    /// (i.e., syntax identities sans module or source offset). Top-level declarations are mapped
    /// onto `-1`.
    internal var syntaxToParent: [Int] = []

    /// A table from scope to the declarations that it contains directly.
    internal var scopeToDeclarations: [Int: [DeclarationIdentity]] = [:]

    /// A table from syntax tree to its type.
    internal var syntaxToType: [Int: AnyTypeIdentity] = [:]

    /// A table from name to its declaration.
    internal var nameToDeclaration: [Int: DeclarationReference] = [:]

  }

  /// The name of the module.
  public let name: Name

  /// The position of `self` in the containing program.
  public let identity: Program.ModuleIdentity

  /// The diagnostics accumulated during compilation.
  public private(set) var diagnostics = DiagnosticSet()

  /// The dependencies of the module.
  public private(set) var dependencies: [Module.Name] = []

  /// The source files in the module.
  internal private(set) var sources = OrderedDictionary<FileName, SourceContainer>()

  /// Creates an empty module with the given name and identity.
  public init(name: Name, identity: Program.ModuleIdentity) {
    self.name = name
    self.identity = identity
  }

  /// Adds a dependency to this module.
  public mutating func addDependency(_ d: Module.Name) {
    if !dependencies.contains(d) {
      dependencies.append(d)
    }
  }

  /// Adds a diagnostic to this module.
  ///
  /// - requires: The diagnostic relates to a source in `self`.
  public mutating func addDiagnostic(_ d: Diagnostic) {
    precondition(sources.keys.contains(d.site.source.name))
    diagnostics.insert(d)
  }

  /// Adds a source file to this module.
  public mutating func addSource(
    _ s: SourceFile
  ) -> (inserted: Bool, identity: Program.SourceFileIdentity) {
    if let f = sources.index(forKey: s.name) {
      return (inserted: false, identity: .init(module: identity, offset: f))
    } else {
      let f = Program.SourceFileIdentity(module: identity, offset: sources.count)
      sources[s.name] = .init(identity: f, source: s)
      let parser = Parser(s, insertingNodesIn: f)
      let declarations = parser.parseTopLevelDeclarations(in: &self)
      sources[s.name]!.topLevelDeclarations.append(contentsOf: declarations)
      return (inserted: true, identity: f)
    }
  }

  /// Inserts `child` into `self` in the bucket of `file`.
  public mutating func insert<T: Syntax>(_ child: T, in file: Program.SourceFileIdentity) -> T.ID {
    assert(file.module == identity)
    return modify(&sources.values[file.offset]) { (f) in
      let d = f.syntax.count
      f.syntax.append(.init(child))
      f.syntaxToKind.append(.init(T.self))
      f.syntaxToParent.append(-1)
      return T.ID(uncheckedFrom: .init(file: file, offset: d))
    }
  }

  /// Inserts `child` into `self` in the scope of `parent`.
  public mutating func insert<T: Expression>(_ child: T, in parent: ScopeIdentity) -> T.ID {
    let i = insert(child, in: parent.file)
    if let p = parent.node {
      sources.values[parent.file.offset].syntaxToParent[i.offset] = p.offset
    }
    return i
  }

  /// Replaces the node identified by `n` by `newValue`.
  ///
  /// The result of `kind(of: n)` denotes `T` after this method returns. No other property of `n`
  /// is changed. The children of the node currently identified by `n` that are not children of
  /// `newValue` are notionally removed from the tree after this method returns. 
  public mutating func replace<T: Expression>(_ n: ExpressionIdentity, for replacement: T) {
    assert(n.module == identity)
    modify(&sources.values[n.file.offset]) { (f) in
      f.syntax[n.offset] = .init(replacement)
      f.syntaxToKind[n.offset] = .init(T.self)
    }
  }

  /// The nodes in `self`'s abstract syntax tree.
  public var syntax: some Collection<AnySyntaxIdentity> {
    let all = sources.values.enumerated().map { (f, s) in
      s.syntax.indices.lazy.map { (n) in
        AnySyntaxIdentity(file: .init(module: identity, offset: f), offset: n)
      }
    }
    return all.joined()
  }

  /// The identities of the source files in `self`.
  public var sourceFileIdentities: [Program.SourceFileIdentity] {
    (0 ..< sources.count).map({ (s) in Program.SourceFileIdentity(module: identity, offset: s) })
  }

  /// The top-level declarations in `self`.
  public var topLevelDeclarations: some Collection<DeclarationIdentity> {
    sources.values.map(\.topLevelDeclarations).joined()
  }

  /// Projects the source file identified by `f`.
  internal subscript(f: Program.SourceFileIdentity) -> SourceContainer {
    _read {
      assert(f.module == identity)
      yield sources.values[f.offset]
    }
    _modify {
      assert(f.module == identity)
      yield &sources.values[f.offset]
    }
  }

  /// Projects the node identified by `n`.
  internal subscript<T: SyntaxIdentity>(n: T) -> any Syntax {
    _read {
      assert(n.module == identity)
      yield sources.values[n.file.offset].syntax[n.offset].wrapped
    }
  }

  /// Projects the node identified by `n`.
  internal subscript<T: Syntax>(n: T.ID) -> T {
    assert(n.module == identity)
    return sources.values[n.file.offset].syntax[n.offset].wrapped as! T
  }

  /// Returns the kind of `n`.
  internal func kind<T: SyntaxIdentity>(of n: T) -> SyntaxKind {
    assert(n.module == identity)
    return self[n.file].syntaxToKind[n.offset]
  }

  /// Assigns a type to `n`.
  internal mutating func setType<T: SyntaxIdentity>(_ t: AnyTypeIdentity, for n: T) {
    assert(n.module == identity)
    let u = sources.values[n.file.offset].syntaxToType[n.offset].wrapIfEmpty(t)
    assert(t == u, "inconsistent type assignment")
  }

  /// Sets the declaration to which `n` refers.
  internal mutating func bind(_ n: NameExpression.ID, to r: DeclarationReference) {
    assert(n.module == identity)
    let s = sources.values[n.file.offset].nameToDeclaration[n.offset].wrapIfEmpty(r)
    assert(r == s, "inconsistent name binding")
  }

  /// Returns the type assigned to `n`, if any.
  internal func type<T: SyntaxIdentity>(assignedTo n: T) -> AnyTypeIdentity? {
    assert(n.module == identity)
    return sources.values[n.file.offset].syntaxToType[n.offset]
  }

  /// Returns the declaration referred to by `n`, if any.
  internal func declaration(referredToBy n: NameExpression.ID) -> DeclarationReference? {
    assert(n.module == identity)
    return sources.values[n.file.offset].nameToDeclaration[n.offset]
  }

}

extension Module: Archivable {

  /// The context of the serialization/deserialization of a module.
  internal struct SerializationContext {

    /// A mapping from archived module identity to its new value.
    internal var modules = OrderedDictionary<Program.ModuleIdentity, Program.ModuleIdentity>()

    /// A mapping from file name to its contents.
    internal var sources = OrderedDictionary<FileName, SourceContainer>()

  }

  /// Reads an instance of `self` from `archive`.
  ///
  /// This method is meant to be called by `Program.load(module:from:)`, which passes `context` as
  /// an instance of `ModuleIdentityMap` associating a module name to its identity in the program.
  public init<A>(from archive: inout ReadableArchive<A>, in context: inout Any) throws {
    let identities = context as? Program.ModuleIdentityMap ?? fatalError("bad context")
    var newContext = SerializationContext()

    // <module name>
    let name = try archive.read(Name.self, in: &context)
    newContext.modules[0] = identities[name]!

    // <dependency count> <dependency name> ...
    let dependencyCount = try archive.readUnsignedLEB128()
    var dependencies: [Module.Name] = []
    for i in 0 ..< dependencyCount {
      let d = try archive.read(Name.self, in: &context)
      dependencies.append(d)
      newContext.modules[Program.ModuleIdentity(i + 1)] = identities[d]
    }

    // <source count> <identity> <contents> ...
    let sourceCount = try Int(archive.readUnsignedLEB128())
    for _ in 0 ..< sourceCount {
      let i = try archive.read(rawValueOf: Program.SourceFileIdentity.self)!
      let s = try archive.read(SourceFile.self)
      newContext.sources[s.name] = .init(identity: i, source: s, syntax: [])
    }

    // The remainder of the module is serialized in a new context.
    for i in 0 ..< sourceCount {
      let syntaxCount = try archive.readUnsignedLEB128()
      for _ in 0 ..< syntaxCount {
        var c = newContext as Any
        let n = try archive.read(AnySyntax.self, in: &c)
        newContext = c as! SerializationContext
        modify(&newContext.sources.values[i]) { (f) in
          f.syntax.append(n)
          f.syntaxToKind.append(.init(Swift.type(of: n.wrapped)))
        }
      }
    }

    self.init(name: name, identity: identities[name]!)
    self.sources = newContext.sources
  }

  /// Serializes `self` to `archive`.
  ///
  /// This method is meant to be called by `Program.write(module:to:)`, which passes `context` as
  /// an instance of `ModuleIdentityMap` associating a module name to its identity in the program.
  public func write<A>(to archive: inout WriteableArchive<A>, in context: inout Any) throws {
    let identities = context as? Program.ModuleIdentityMap ?? fatalError("bad context")
    var newContext = SerializationContext()

    // <module name>
    try archive.write(name, in: &context)
    newContext.modules[identity] = 0

    // <dependency count> <dependency name> ...
    archive.write(unsignedLEB128: dependencies.count)
    for d in dependencies {
      try archive.write(d, in: &context)
      newContext.modules[identities[d]!] = newContext.modules.count
    }

    // <source count> <identity> <contents> ...
    archive.write(unsignedLEB128: sources.count)
    for (f, s) in sources {
      try archive.write(rawValueOf: s.identity, in: &context)
      try archive.write(s.source, in: &context)
      newContext.sources[f] = s
    }

    // The remainder of the module is deserialized in a new context.
    var c = newContext as Any
    for s in sources.values {
      archive.write(unsignedLEB128: s.syntax.count)
      for n in s.syntax { try archive.write(n, in: &c) }
    }
  }

}
