/// Information about the memory layout of a value.
public struct Metatype {

  /// The number of bytes occupied by an instance.
  public let size: Int

  /// The alignment of an intance.
  public let alignment: Int

  /// The offset of each stored field of an instance.
  public let offsets: [Int]

  /// Returns the number of bytes from the start of one instance to the start of the next when
  /// stored in contiguous memory.
  public var stride: Int {
    let x = size.rounded(upToNearestMultipleOf: alignment)
    return x < 1 ? 1 : x
  }

}
