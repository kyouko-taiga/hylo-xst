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
  func positive(_ input: ProgramDescription) throws {
    let (program, _) = try compile(input)
    XCTAssertFalse(program.containsError, "program contains one or more errors")
  }

  /// Compiles `input` expecting at least one compilation error.
  func negative(_ input: ProgramDescription) throws {
    let (program, expectations) = try compile(input)
    XCTAssert(program.containsError, "program compiled but an error was expected")
    try assertExpectations(expectations, program.diagnostics)
  }

  /// Compiles `input` into `p` and returns expected diagnostics for each compiled source file.
  private func compile(_ input: ProgramDescription) throws -> (Program, [FileName: String]) {
    var p = Program()
    let m = p.demandIdentity(module: "Test")

    var expectations: [FileName: String] = [:]
    try input.forEachSourceURL { (u) in
      let source = try SourceFile(contentsOf: u)
      _ = p[m].addSource(source)

      let v = u.deletingPathExtension().appendingPathExtension("expected")
      let expected = try? String(contentsOf: v, encoding: .utf8)
      expectations[source.name] = expected
    }

    return (p, expectations)
  }

  /// Asserts that the expected diagnostics of each source file in `expectations` matches those
  /// obtained during compilation.
  private func assertExpectations<T: Collection<Diagnostic>>(
    _ expectations: [FileName: String],
    _ diagnostics: T
  ) throws {
    if expectations.isEmpty { return }

    var observations: [FileName: [Diagnostic]] = [:]
    for d in diagnostics {
      observations[d.site.source.name, default: []].append(d)
    }

    let root = URL(filePath: #filePath).deletingLastPathComponent()
    for (n, e) in expectations {
      var o = ""
      for d in observations[n, default: []].sorted() {
        d.render(into: &o, showingPaths: .relative(to: root), style: .unstyled)
      }
      if o != e {
        guard case .local(let u) = n else { break }
        let v = u.deletingPathExtension().appendingPathExtension("observed")
        try o.write(to: v, atomically: true, encoding: .utf8)
        XCTFail("output does not match expected result")
      }
    }
  }

}
