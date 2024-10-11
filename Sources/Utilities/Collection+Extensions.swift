extension Collection {

  /// The unique element of `self` if `self` contains exactly one element; otherwise, `nil`.
  public var uniqueElement: Element? {
    count == 1 ? self[startIndex] : nil
  }

}
