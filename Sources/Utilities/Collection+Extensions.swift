extension Collection {

  /// The unique element of `self` if `self` contains exactly one element; otherwise, `nil`.
  public var uniqueElement: Element? {
    count == 1 ? self[startIndex] : nil
  }

  /// The first element of `self` and its suffix after its first index or `nil` if `self` is empty.
  public var headAndTail: (head: Element, tail: SubSequence)? {
    if isEmpty { return nil }
    return (head: self[startIndex], tail: self[index(after: startIndex)...])
  }

}
