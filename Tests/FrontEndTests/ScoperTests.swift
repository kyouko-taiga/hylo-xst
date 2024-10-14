import FrontEnd
import XCTest

final class ScoperTests: XCTestCase {

  func testParent() async throws {
    let p = await Program.test.scoped()
    for a in p.select(.kind(AssociatedTypeDeclaration.self)) {
      let n = try XCTUnwrap(p.parent(containing: a).node)
      XCTAssertEqual(p.kind(of: n), .init(TraitDeclaration.self))
    }
  }

}
