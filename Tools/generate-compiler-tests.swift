#!/usr/bin/swift
import Foundation

/// The root path of the compiler test target.
private let root = URL(filePath: #filePath)
  .deletingLastPathComponent()
  .deletingLastPathComponent()
  .appending(components: "Tests", "CompilerTests")

/// The directory in which test cases are generated.
private let output = root.appending(component: "CompilerTests+GeneratedTests.swift")

/// The root of the directory containing negative tests.
private let negative = root.appending(component: "negative", directoryHint: .isDirectory)

/// The root of the directory containing positive tests.
private let positive = root.appending(component: "positive", directoryHint: .isDirectory)

/// Returns the URLs in `suite` having a ".hylo" or ".package" extension.
private func testCases(_ suite: URL) throws -> [URL] {
  let urls = try FileManager.default.contentsOfDirectory(
    at: suite,
    includingPropertiesForKeys: nil, options: .skipsHiddenFiles)
  return urls.filter { (u) in u.pathExtension == "hylo" || u.pathExtension == "package" }
}

func testCaseIdentifier(_ testCase: URL) -> String {
  testCase.deletingPathExtension().lastPathComponent.replacingOccurrences(of: "-", with: "_")
}

private func main() throws {
  var result = "extension CompilerTests {\n"

  for u in try testCases(negative) {
    let i = testCaseIdentifier(u)
    result += """

      func test_negative_\(i)() async throws {
        try await negative(.init("\(i)", "\(u.absoluteURL.path())"))
      }

    """
  }

  for u in try testCases(positive) {
    let i = testCaseIdentifier(u)
    result += """

      func test_positive_\(i)() async throws {
        try await positive(.init("\(i)", "\(u.absoluteURL.path())"))
      }

    """
  }

  result.append("\n}")
  try result.write(to: output, atomically: true, encoding: .utf8)
}

try main()
