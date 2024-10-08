import FrontEnd
import XCTest

final class SourceSpanTests: XCTestCase {

  func testInitRegionIn() {
    let f: SourceFile = "Hello."
    let i = f.startIndex
    let s = SourceSpan(i ..< f.index(i, offsetBy: 2), in: f)
    XCTAssertEqual(s.region, i ..< f.index(i, offsetBy: 2))
  }

  func testStart() {
    let f: SourceFile = "Hello."
    let s = f.span
    XCTAssertEqual(s.start, .init(f.startIndex, in: f))
  }

  func testEnd() {
    let f: SourceFile = "Hello."
    let s = f.span
    XCTAssertEqual(s.end, .init(f.endIndex, in: f))
  }

  func testExtendedToCover() {
    let f: SourceFile = "Hello."
    let i0 = f.startIndex
    let i1 = f.index(i0, offsetBy: 2)
    let i2 = f.index(i0, offsetBy: 4)
    let i3 = f.index(i0, offsetBy: 6)

    let s = SourceSpan(i1 ..< i2, in: f)
    XCTAssertEqual(s.extended(toCover: .init(i0 ..< i2, in: f)).region, i0 ..< i2)
    XCTAssertEqual(s.extended(toCover: .init(i1 ..< i3, in: f)).region, i1 ..< i3)
    XCTAssertEqual(s.extended(toCover: .init(i0 ..< i3, in: f)).region, i0 ..< i3)
  }

  func testExtendedUpTo() {
    let f: SourceFile = "Hello."
    let i0 = f.startIndex
    let i1 = f.index(i0, offsetBy: 2)
    let i2 = f.index(i0, offsetBy: 4)

    let s = SourceSpan(i0 ..< i1, in: f)
    XCTAssertEqual(s.extended(upTo: i0).region, i0 ..< i1)
    XCTAssertEqual(s.extended(upTo: i1).region, i0 ..< i1)
    XCTAssertEqual(s.extended(upTo: i2).region, i0 ..< i2)
  }

  func testEmpty() {
    let f: SourceFile = "Hello."
    let p = SourcePosition(f.startIndex, in: f)
    let s = SourceSpan.empty(at: p)
    XCTAssertEqual(s.region, f.startIndex ..< f.startIndex)
  }

  func testDescription() {
    let f: SourceFile = "Hello."
    XCTAssertEqual(f.span.description, "virtual://1ssiyy33rbj6z:1.1-7")
    let g: SourceFile = "A\nB"
    XCTAssertEqual(g.span.description, "virtual://3ahohnnbwwf82:1.1-2:2")
  }

}
