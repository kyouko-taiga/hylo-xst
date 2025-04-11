import ArgumentParser
import Foundation
import FrontEnd
import Utilities

import Archivist

/// The top-level command of `hc`.
@main struct Driver: AsyncParsableCommand {

  /// Configuration for this command.
  public static let configuration = CommandConfiguration(commandName: "hc")

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
    var program = Program()
    let module = program.demandModule(productName(inputs))

    try parse(inputs: inputs, into: &program[module])
    await assignScopes(of: module, in: &program)
    assignTypes(of: module, in: &program)

    let c = treePrinterConfiguration(for: treePrinterFlags)
    for d in program.select(.and(.from(module), .topLevel)) {
      print(program.show(d, configuration: c))
    }
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

  /// Parses the input files in `inputs` and adds them to `module`.
  @MainActor
  private func parse(inputs: [URL], into module: inout Module) throws {
    let clock = ContinuousClock()
    let elapsed = try clock.measure {
      for url in inputs {
        if url.hasDirectoryPath {
          try SourceFile.forEach(in: url) { (f) in module.addSource(f) }
        } else if url.pathExtension == "hylo" {
          try module.addSource(SourceFile(contentsOf: url))
        } else {
          throw ValidationError("unexpected input: \(url.relativePath)")
        }
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
  private func productName(_ inputs: [URL]) -> String {
    if let u = inputs.uniqueElement {
      let n = u.deletingPathExtension().lastPathComponent.drop(while: { $0 == "." })
      if !n.isEmpty {
        return String(n)
      }
    }
    return "Main"
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
