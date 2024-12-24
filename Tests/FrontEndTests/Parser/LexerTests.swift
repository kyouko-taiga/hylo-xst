import FrontEnd
import XCTest

final class LexerTests: XCTestCase {

  func testLineComments() throws {
    let input: SourceFile = """
      Hello // comment
      World
      """
    var scanner = Lexer(tokenizing: input)
    try assertNext(from: &scanner, is: .name)
    try assertNext(from: &scanner, is: .name)
    XCTAssertNil(scanner.next())
  }

  func testBlockComments() throws {
    let input: SourceFile = """
      Hello /* comment-0 *//* /* comment-1 */ comment-2 */
      World
      """
    var scanner = Lexer(tokenizing: input)
    try assertNext(from: &scanner, is: .name)
    try assertNext(from: &scanner, is: .name)
    XCTAssertNil(scanner.next())
  }

  func testUnterminatedBlockComment() throws {
    var scanner = Lexer(tokenizing: "/* /* comment-1 */ comment-2 World")
    try assertNext(from: &scanner, is: .unterminatedBlockComment)
    XCTAssertNil(scanner.next())
  }

  func testDelimiters() throws {
    var scanner = Lexer(tokenizing: "<<({[]})>>")
    try assertNext(from: &scanner, is: .leftAngle)
    try assertNext(from: &scanner, is: .leftAngle)
    try assertNext(from: &scanner, is: .leftParenthesis)
    try assertNext(from: &scanner, is: .leftBrace)
    try assertNext(from: &scanner, is: .leftBracket)
    try assertNext(from: &scanner, is: .rightBracket)
    try assertNext(from: &scanner, is: .rightBrace)
    try assertNext(from: &scanner, is: .rightParenthesis)
    try assertNext(from: &scanner, is: .rightAngle)
    try assertNext(from: &scanner, is: .rightAngle)
    XCTAssertNil(scanner.next())
  }

  func testError() throws {
    var scanner = Lexer(tokenizing: "\0.")
    try assertNext(from: &scanner, is: .error)
    try assertNext(from: &scanner, is: .dot)
    XCTAssertNil(scanner.next())
  }

  func testIdentifier() throws {
    var scanner = Lexer(tokenizing: "a _a _0 \u{3042}\u{3042} _")
    try assertNext(from: &scanner, is: .name, withValue: "a")
    try assertNext(from: &scanner, is: .name, withValue: "_a")
    try assertNext(from: &scanner, is: .name, withValue: "_0")
    try assertNext(from: &scanner, is: .name, withValue: "\u{3042}\u{3042}")
    try assertNext(from: &scanner, is: .underscore)
    XCTAssertNil(scanner.next())
  }

  func testKeywords() throws {
    let input: SourceFile = """
      conformance extension false fun let import infix init inout internal postfix prefix private
      public return set sink struct trait true type typealias var
      """
    var scanner = Lexer(tokenizing: input)
    try assertNext(from: &scanner, is: .conformance)
    try assertNext(from: &scanner, is: .extension)
    try assertNext(from: &scanner, is: .false)
    try assertNext(from: &scanner, is: .fun)
    try assertNext(from: &scanner, is: .let)
    try assertNext(from: &scanner, is: .import)
    try assertNext(from: &scanner, is: .infix)
    try assertNext(from: &scanner, is: .`init`)
    try assertNext(from: &scanner, is: .inout)
    try assertNext(from: &scanner, is: .internal)
    try assertNext(from: &scanner, is: .postfix)
    try assertNext(from: &scanner, is: .prefix)
    try assertNext(from: &scanner, is: .private)
    try assertNext(from: &scanner, is: .public)
    try assertNext(from: &scanner, is: .return)
    try assertNext(from: &scanner, is: .set)
    try assertNext(from: &scanner, is: .sink)
    try assertNext(from: &scanner, is: .struct)
    try assertNext(from: &scanner, is: .trait)
    try assertNext(from: &scanner, is: .true)
    try assertNext(from: &scanner, is: .type)
    try assertNext(from: &scanner, is: .typealias)
    try assertNext(from: &scanner, is: .var)
    XCTAssertNil(scanner.next())
  }

  func testOperator() throws {
    var scanner = Lexer(tokenizing: "<= ++ & &&& -> ==")
    try assertNext(from: &scanner, is: .leftAngle)
    try assertNext(from: &scanner, is: .assign)
    try assertNext(from: &scanner, is: .operator, withValue: "++")
    try assertNext(from: &scanner, is: .ampersand)
    try assertNext(from: &scanner, is: .operator, withValue: "&&&")
    try assertNext(from: &scanner, is: .arrow)
    try assertNext(from: &scanner, is: .equal)
    XCTAssertNil(scanner.next())
  }

  func testPunctuation() throws {
    var scanner = Lexer(tokenizing: ",.: :: ;")
    try assertNext(from: &scanner, is: .comma)
    try assertNext(from: &scanner, is: .dot)
    try assertNext(from: &scanner, is: .colon)
    try assertNext(from: &scanner, is: .doubleColon)
    try assertNext(from: &scanner, is: .semicolon)
    XCTAssertNil(scanner.next())
  }

}

private func assertNext(
  from scanner: inout Lexer, is expected: Token.Kind, withValue text: String? = nil,
  file: StaticString = #file, line: UInt = #line
) throws {
  let next = try XCTUnwrap(scanner.next())
  XCTAssertEqual(next.kind, expected, file: file, line: line)
  if let s = text {
    XCTAssertEqual(String(next.text), s, file: file, line: line)
  }
}
