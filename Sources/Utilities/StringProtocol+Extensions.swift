extension StringProtocol {

  /// Returns `self` indented by two spaces.
  public var indented: String {
    (self.split(separator: "\n") as [SubSequence]).lazy
      .map({ (line) in "  " + line })
      .joined(separator: "\n")
  }

  /// Returns the indices of the start of each line, in order.
  public func lineBoundaries() -> [Index] {
    var r = [startIndex]
    var remainder = self[...]
    while !remainder.isEmpty, let i = remainder.firstIndex(where: \.isNewline) {
      let j = index(after: i)
      r.append(j)
      remainder = remainder[j...]
    }
    return r
  }

}

extension String.StringInterpolation {

  /// Appends the string descriptions of the elements in `list` separated by `separator`.
  public mutating func appendInterpolation<L: Sequence>(
    list: L, joinedBy separator: String = ", "
  ) {
    appendLiteral(list.descriptions(joinedBy: separator))
  }

}
