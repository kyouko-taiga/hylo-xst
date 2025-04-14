import Archivist
import ArgumentParser
import Foundation
import FrontEnd
import Utilities
import StandardLibrary

/// The top-level command of `hc`.
@main struct Driver: AsyncParsableCommand {

  /// Configuration for this command.
  public static let configuration = CommandConfiguration(commandName: "hc")

  /// The paths at which libraries may be found.
  @Option(
    name: [.customShort("L")],
    help: ArgumentHelp(
      "Add a directory to the library search path.",
      valueName: "path"),
    transform: URL.init(fileURLWithPath:))
  private var librarySearchPaths: [URL] = []

  /// The path containing cached module data.
  @Option(
    name: [.customLong("module-cache")],
    help: ArgumentHelp(
      "Specify the module cache path.",
      valueName: "path"),
    transform: URL.init(fileURLWithPath:))
  private var moduleCachePath: URL?

  @Flag(help: "Disable caching.")
  private var noCaching: Bool = false

  /// The kind of output that should be produced by the compiler.
  @Option(
    name: [.customLong("emit")],
    help: ArgumentHelp(
      "Produce the specified output: Possible values are: ast, typed-ast",
      valueName: "output-type"))
  private var outputType: OutputType = .typedAST

  /// The configuration of the tree printer.
  @Flag(help: "Tree printer configuration")
  private var treePrinterFlags: [TreePrinterFlag] = []

  /// `true` iff verbose information about compilation should be printed to the standard output.
  @Flag(
    name: [.short, .long],
    help: "Use verbose output.")
  private var verbose: Bool = false

  /// The input files and directories passed to the command.
  @Argument(transform: URL.init(fileURLWithPath:))
  private var inputs: [URL] = []

  /// Creates a new instance with default options.
  public init() {}

  /// Executes the command.
  @MainActor
  public mutating func run() async throws {
    try configureSearchPaths()

    // Load the standard library.
    var program = Program()
    try await load(.standardLibrary, withSourcesAt: standardLibrarySources, into: &program)

    // Create a module for the product being compiled.
    let product = productName(inputs)
    note("start compiling \(product)")
    let module = program.demandModule(product)
    program[module].addDependency(.standardLibrary)

    let sources = try sourceFiles(recursivelyContainedIn: inputs)
    parse(sources, into: &program[module])

    await assignScopes(of: module, in: &program)
    assignTypes(of: module, in: &program)

    let c = treePrinterConfiguration(for: treePrinterFlags)
    for d in program.select(.and(.from(module), .topLevel)) {
      print(program.show(d, configuration: c))
    }

    let a = try program.archive(module: module)
    print(a)
  }

  /// Sets up the value of search paths for locating libraries and cached artefacts.
  private mutating func configureSearchPaths() throws {
    let fm = FileManager.default
    if let m = moduleCachePath {
      librarySearchPaths.append(m)
    } else {
      let m = fm.temporaryDirectory.appending(path: ".hylocache")
      try fm.createDirectory(at: m, withIntermediateDirectories: true)
      librarySearchPaths.append(m)
      moduleCachePath = m
    }

    librarySearchPaths = .init(librarySearchPaths.uniqued())
    librarySearchPaths.removeDuplicates()
  }

  /// Loads `module`, whose sources are in `root`, into `program`.
  ///
  /// If `noCaching` is not set, the module is loaded from cache if an archive is found and its
  /// fingerprint matches the fingerprint of the source files in `root`. Otherwise, the module is
  /// compiled from sources and an archive is stored at `moduleCachePath`. If `noCaching` is set,
  /// the module is unconditionally compiled from sources and no archive is stored.
  private mutating func load(
    _ module: Module.Name, withSourcesAt root: URL,
    into program: inout Program
  ) async throws {
    note("start loading \(module)")

    // Compute a fingerprint of all source files.
    var sources: [SourceFile] = []
    try SourceFile.forEach(in: root) { (s) in
      sources.append(s)
    }

    // Attempt to load the module from disk.
    if !noCaching, let data = archive(of: module) {
      let h = SourceFile.fingerprint(contentsOf: sources)
      var a = ReadableArchive(data)
      let (_, fingerprint) = try Module.header(&a)
      if h == fingerprint {
        a = ReadableArchive(data)
        try program.load(module: module, from: &a)
        return
      } else {
        note("archive is out of date")
      }
    }

    // Compile the module from sources.
    let m = program.demandModule(module)
    await parse(sources, into: &program[m])
    await assignScopes(of: m, in: &program)
    await assignTypes(of: m, in: &program)

    if !noCaching {
      let archive = try program.archive(module: m)
      try archive.write(
        into: moduleCachePath!.appending(component: module.rawValue + ".hylomodule"))
    }
  }

  /// Returns an array with all the source files in `inputs` and their subdirectories.
  private func sourceFiles(recursivelyContainedIn inputs: [URL]) throws -> [SourceFile] {
    var sources: [SourceFile] = []
    for url in inputs {
      if url.hasDirectoryPath {
        try SourceFile.forEach(in: url) { (f) in sources.append(f) }
      } else if url.pathExtension == "hylo" {
        try sources.append(SourceFile(contentsOf: url))
      } else {
        throw ValidationError("unexpected input: \(url.relativePath)")
      }
    }
    return sources
  }

  /// Searches for an archive of `module` in `librarySearchPaths`, returning it if found.
  private func archive(of module: Module.Name) -> Data? {
    for prefix in librarySearchPaths {
      let path = prefix.appending(path: module.rawValue + ".hylomodule")
      return try? Data(contentsOf: path)
    }
    return nil
  }

  /// If `module` contains errors, renders all its diagnostics and exits with `ExitCode.failure`.
  /// Otherwise, does nothing.
  @MainActor
  private func exitOnError(_ module: Module) {
    if module.containsError {
      render(module.diagnostics)
      Driver.exit(withError: ExitCode.failure)
    }
  }

  /// Renders the given diagnostics to the standard error.
  @MainActor
  private func render<T: Sequence<Diagnostic>>(_ ds: T) {
    let s: Diagnostic.TextOutputStyle = ProcessInfo.ansiTerminalIsConnected ? .styled : .unstyled
    var o = ""
    for d in ds {
      d.render(into: &o, showingPaths: .absolute, style: s)
    }
    print(o, to: &Driver.standardError)
  }

  /// Parses the source files in `inputs` and adds them to `module`.
  @MainActor
  private func parse(_ sources: [SourceFile], into module: inout Module) {
    let clock = ContinuousClock()
    let elapsed = clock.measure {
      for s in sources {
        module.addSource(s)
      }
    }
    note("parsed \(module.sourceFileIdentities.count) files in \(elapsed.human)")
    exitOnError(module)
  }

  /// Assignes the trees in `module` to their scopes, exiting if an error occurred.
  @MainActor
  private func assignScopes(of module: Program.ModuleIdentity, in program: inout Program) async {
    let clock = ContinuousClock()
    let elapsed = await clock.measure {
      await program.assignScopes(module)
    }
    note("scoping completed in \(elapsed.human)")
    exitOnError(program[module])
  }

  /// Assigns the trees in `module` to their types, exiting if an error occured.
  @MainActor
  private func assignTypes(of module: Program.ModuleIdentity, in program: inout Program) {
    let clock = ContinuousClock()
    let elapsed = clock.measure {
      program.assignTypes(module)
    }
    note("typing completed in \(elapsed.human)")
    exitOnError(program[module])
  }

  /// Writes `message` to the standard output iff `self.verbose` is `true`.
  private func note(_ message: @autoclosure () -> String) {
    if verbose {
      print(message())
    }
  }

  /// Returns the configuration corresponding to the given `flags`.
  private func treePrinterConfiguration(
    for flags: [TreePrinterFlag]
  ) -> TreePrinter.Configuration {
    .init(useVerboseTypes: flags.contains(.verboseTypes))
  }

  /// If `inputs` contains a single URL `u` whose path is non-empty, returns the last component of
  /// `u` without any path extension and stripping all leading dots. Otherwise, returns "Main".
  private func productName(_ inputs: [URL]) -> Module.Name {
    if let u = inputs.uniqueElement {
      let n = u.deletingPathExtension().lastPathComponent.drop(while: { $0 == "." })
      if !n.isEmpty {
        return .init(String(n))
      }
    }
    return .init("Main")
  }

  /// The type of the output files to generate.
  private enum OutputType: String, ExpressibleByArgument {

    /// Abstract syntax tree before typing.
    case ast = "ast"

    /// Abstract syntax tree after typing.
    case typedAST = "typed-ast"

  }

  /// Tree printing flags.
  private enum TreePrinterFlag: String, EnumerableFlag {

    /// Prints a verbose representation of type trees.
    case verboseTypes = "print-verbose-types"

    static func name(for value: TreePrinterFlag) -> NameSpecification {
      .customLong(value.rawValue)
    }

  }

}

extension ProcessInfo {

  /// `true` iff the terminal supports coloring.
  fileprivate static let ansiTerminalIsConnected =
    !["", "dumb", nil].contains(processInfo.environment["TERM"])

}

extension ContinuousClock.Instant.Duration {

  /// The value of `self` in nanoseconds.
  fileprivate var ns: Int64 { components.attoseconds / 1_000_000_000 }

  /// The value of `self` in microseconds.
  fileprivate var μs: Int64 { ns / 1_000 }

  /// The value of `self` in milliseconds.
  fileprivate var ms: Int64 { μs / 1_000 }

  /// A human-readable representation of `self`.
  fileprivate var human: String {
    guard abs(ns) >= 1_000 else { return "\(ns)ns" }
    guard abs(μs) >= 1_000 else { return "\(μs)μs" }
    guard abs(ms) >= 1_000 else { return "\(ms)ms" }
    return formatted()
  }

}
