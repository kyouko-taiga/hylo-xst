@testable import FrontEnd
import XCTest

final class TypeStoreTests: XCTestCase {

  func testDemandError() {
    var store = TypeStore()
    let t = ErrorType()
    let i = store.demand(t)
    XCTAssertEqual(i.erased, AnyTypeIdentity.error)
    XCTAssertEqual(store[i], t)
  }

  func testDemandVoid() {
    var store = TypeStore()
    let t = Tuple(elements: [])
    let i = store.demand(t)
    XCTAssertEqual(i.erased, AnyTypeIdentity.void)
    XCTAssertEqual(store[i], t)
  }

  func testDemandNever() {
    var store = TypeStore()
    let t = Union(elements: [])
    let i = store.demand(t)
    XCTAssertEqual(i.erased, AnyTypeIdentity.never)
    XCTAssertEqual(store[i], t)
  }

  func testDemand() {
    var store = TypeStore()
    let t = Tuple(elements: [.init(label: "a", type: .void)])
    let i = store.demand(t)
    XCTAssertEqual(store[i], t)
    let j = store.demand(t)
    XCTAssertEqual(i, j)
  }

}
