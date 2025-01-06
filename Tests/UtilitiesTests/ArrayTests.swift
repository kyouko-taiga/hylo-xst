import Utilities
import XCTest

final class ArrayTests: XCTestCase {

  func testInitWithMinimumCapacity() {
    let a = Array<Int>(minimumCapacity: 100)
    XCTAssert(a.capacity >= 100)
  }

}
