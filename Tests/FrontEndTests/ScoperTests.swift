import FrontEnd
import XCTest

final class ScoperTests: XCTestCase {

  func testParent() async throws {
    let p = await Program.test.scoped()
    for a in p.select(.tag(AssociatedTypeDeclaration.self)) {
      let n = try XCTUnwrap(p.parent(containing: a).node)
      XCTAssertEqual(p.tag(of: n), .init(TraitDeclaration.self))
    }
  }

}
