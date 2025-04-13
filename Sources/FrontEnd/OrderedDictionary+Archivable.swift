import Archivist
import OrderedCollections

//extension OrderedDictionary: Archivable where Key: Archivable, Value: Archivable {
//
//  /// Reads `self` from `archive`, updating `context` with the deserialization state.
//  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
//    let count = try Int(archive.readUnsignedLEB128())
//    self.init()
//    reserveCapacity(count)
//    while self.count < count {
//      let k = try Key(from: &archive, in: &context)
//      let v = try Value(from: &archive, in: &context)
//      self[k] = v
//    }
//  }
//
//  /// Writes `self` to `archive`, updating `context` with the serialization state.
//  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
//    try write(to: &archive) { (e, a) in
//      try e.key.write(to: &a, in: &context)
//      try e.value.write(to: &a, in: &context)
//    }
//  }
//
//}
