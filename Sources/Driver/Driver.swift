import Archivist
import BackEnd
import Foundation
import FrontEnd
import StandardLibrary
import Utilities

/// A helper to drive the compilation of Hylo source files.
public struct Driver {

  /// The path containing cached module data.
  public let moduleCachePath: URL?

  /// The program being compiled by the driver.
  public var program: Program

  /// Creates an instance with the given properties.
  public init(moduleCachePath: URL? = nil) {
    self.moduleCachePath = moduleCachePath
    self.program = .init()
  }

  /// `true` iff the driver should read/write modules from/to the cache.
  public var cachingIsEnabled: Bool {
    moduleCachePath != nil
  }

  /// Parses the source files in `inputs` and adds them to `module`.
  @discardableResult
  public mutating func parse(
    _ sources: [SourceFile], into module: Program.ModuleIdentity
  ) async -> (elapsed: Duration, containsError: Bool) {
    let clock = ContinuousClock()
    let elapsed = clock.measure {
      modify(&program[module]) { (m) in
        for s in sources { m.addSource(s) }
      }
    }
    return (elapsed, program[module].containsError)
  }

  /// Assignes the trees in `module` to their scopes, exiting if an error occurred.
  @discardableResult
  public mutating func assignScopes(
    of module: Program.ModuleIdentity
  ) async -> (elapsed: Duration, containsError: Bool) {
    let clock = ContinuousClock()
    let elapsed = await clock.measure {
      await program.assignScopes(module)
    }
    return (elapsed, program[module].containsError)
  }

  /// Assigns the trees in `module` to their types, exiting if an error occured.
  @discardableResult
  public mutating func assignTypes(
    of module: Program.ModuleIdentity
  ) async -> (elapsed: Duration, containsError: Bool) {
    let clock = ContinuousClock()
    let elapsed = clock.measure {
      program.assignTypes(module)
    }
    return (elapsed, program[module].containsError)
  }

  /// Translates `module` to C++.
  public mutating func translate(
    _ module: Program.ModuleIdentity
  ) async -> (elasped: Duration, translation: (header: String, source: String)) {
    let clock = ContinuousClock()

    // Lowering.
    var lowerer = Lowerer(translating: module, of: program)
    let e0 = clock.measure {
      lowerer.apply()
    }

    // Codegen.
    var renderer = MonomorphizingRenderer(
      rendering: lowerer.ir, loweredFrom: lowerer.release())
    var result = (header: "", source: "")
    let e1 = clock.measure {
      result = renderer.apply()
    }

    program = renderer.release()
    return (e0 + e1, result)
  }

  /// Loads `module`, whose sources are in `root`, into `program`.
  ///
  /// If `moduleCachePath` is set, the module is loaded from cache if an archive is found and its
  /// fingerprint matches the fingerprint of the source files in `root`. Otherwise, the module is
  /// compiled from sources and an archive is stored at `moduleCachePath`. If `moduleCachePath` is
  /// not set, the module is unconditionally compiled from sources and no archive is stored.
  public mutating func load(
    _ module: Module.Name, withSourcesAt root: URL
  ) async throws {
    // Compute a fingerprint of all source files.
    var sources: [SourceFile] = []
    try SourceFile.forEach(in: root) { (s) in
      sources.append(s)
    }

    // Attempt to load the module from disk.
    if cachingIsEnabled, let data = archive(of: module) {
      let h = SourceFile.fingerprint(contentsOf: sources)
      var a = ReadableArchive(data)
      let (_, fingerprint) = try Module.header(&a)
      if h == fingerprint {
        a = ReadableArchive(data)
        try program.load(module: module, from: &a)
        return
      }
    }

    // Compile the module from sources.
    let m = program.demandModule(module)

    await parse(sources, into: m)
    try throwIfContainsError(m)

    await assignScopes(of: m)
    try throwIfContainsError(m)

    await assignTypes(of: m)
    try throwIfContainsError(m)

    if cachingIsEnabled {
      let a = try program.archive(module: m)
      let f = moduleCachePath!.appending(component: module.rawValue + ".hylomodule")
      try a.write(into: f)
    }
  }

  /// Loads the standard library with `load(_:withSourcesAt:)`.
  public mutating func loadStandardLibrary() async throws {
    try await load(.standardLibrary, withSourcesAt: standardLibrarySources)
  }

  /// Searches for an archive of `module` in `librarySearchPaths`, returning it if found.
  public func archive(of module: Module.Name) -> Data? {
    if let prefix = moduleCachePath {
      let path = prefix.appending(path: module.rawValue + ".hylomodule")
      return try? Data(contentsOf: path)
    } else {
      return nil
    }
  }

  private func throwIfContainsError(_ m: Program.ModuleIdentity) throws {
    if program[m].containsError {
      throw CompilationError(diagnostics: .init(program[m].diagnostics))
    }
  }

}
