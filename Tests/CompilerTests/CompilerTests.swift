import FrontEnd
import XCTest

final class CompilerTests: XCTestCase {

  /// The input of a compiler test.
  struct ProgramDescription {

    /// The name of the program.
    let name: String

    /// The root path of the program's sources.
    let root: URL

    /// Creates an instance with the given properties.
    init(_ name: String, _ path: String) {
      self.name = name
      self.root = URL(filePath: path)
    }

    /// `true` iff `self` describes a pacakge.
    var isPackage: Bool { root.pathExtension == "package" }

    /// Calls `action` on each Hylo source URL in the program described by `self`.
    func forEachSourceURL(_ action: (URL) throws -> Void) throws {
      if isPackage {
        try SourceFile.forEachURL(in: root, action)
      } else {
        try action(root)
      }
    }

  }

  /// Compiles `input` expecting no compilation error.
  func positive(_ input: ProgramDescription) async throws {
    let (program, _) = try await compile(input)
    assertSansError(program)
  }

  /// Compiles `input` expecting at least one compilation error.
  func negative(_ input: ProgramDescription) async throws {
    let (program, expectations) = try await compile(input)
    XCTAssert(program.containsError, "program compiled but an error was expected")
    assertExpectations(expectations, program.diagnostics)
  }

  /// Compiles `input` into `p` and returns expected diagnostics for each compiled source file.
  private func compile(_ input: ProgramDescription) async throws -> (Program, [FileName: String]) {
    var p = Program()
    let m = p.demandModule("Test")

    var expectations: [FileName: String] = [:]
    try input.forEachSourceURL { (u) in
      let source = try SourceFile(contentsOf: u)
      _ = p[m].addSource(source)

      let v = u.deletingPathExtension().appendingPathExtension("expected")
      let expected = try? String(contentsOf: v, encoding: .utf8)
      expectations[source.name] = expected
    }

    // Exit if there are parsing errors.
    if p.containsError { return (p, expectations) }

    // Semantic analysis.
    await p.assignScopes(m)
    p.assignTypes(m)

    return (p, expectations)
  }

  /// Asserts that the expected diagnostics of each source file in `expectations` matches those
  /// obtained during compilation.
  private func assertExpectations<T: Collection<Diagnostic>>(
    _ expectations: [FileName: String],
    _ diagnostics: T
  ) {
    if expectations.isEmpty { return }

    let root = URL(filePath: #filePath).deletingLastPathComponent()
    let observations: [FileName: [Diagnostic]] = .init(
      grouping: diagnostics, by: \.site.source.name)

    for (n, e) in expectations {
      var o = ""
      for d in observations[n, default: []].sorted() {
        d.render(into: &o, showingPaths: .relative(to: root), style: .unstyled)
      }

      if o != e {
        XCTFail("output does not match expected result")
        guard case .local(let u) = n else { continue }
        let v = u.deletingPathExtension().appendingPathExtension("observed")
        try? o.write(to: v, atomically: true, encoding: .utf8)
      }
    }
  }

  /// Asserts that `program` does not contain any error.
  private func assertSansError(_ program: Program) {
    if !program.containsError { return }

    XCTFail("program contains one or more errors")
    let root = URL(filePath: #filePath).deletingLastPathComponent()
    let observations: [FileName: [Diagnostic]] = .init(
      grouping: program.diagnostics, by: \.site.source.name)

    for case (.local(let u), let ds) in observations {
      var o = ""
      for d in ds.sorted() {
        d.render(into: &o, showingPaths: .relative(to: root), style: .unstyled)
        let v = u.deletingPathExtension().appendingPathExtension("observed")
        try? o.write(to: v, atomically: true, encoding: .utf8)
      }
    }
  }

}
