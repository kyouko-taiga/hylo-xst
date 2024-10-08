import Archivist

extension Archivable {

  /// Writes `self` to an archive and returns its deserialization.
  func storedAndLoaded() throws -> Self {
    var w = WriteableArchive(BinaryBuffer())
    try w.write(self)
    var r = ReadableArchive(w.finalize())
    return try r.read(Self.self)
  }

}
