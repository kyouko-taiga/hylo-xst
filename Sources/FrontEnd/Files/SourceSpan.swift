import Archivist
import Utilities

/// A half-open range of textual positions in a source file.
public struct SourceSpan: Hashable {

  /// The source file containing the region that `self` represents.
  public let source: SourceFile

  /// The bounds of the region that `self` represents.
  public let region: Range<SourceFile.Index>

  /// Creates an instance representing `source[region]`.
  public init(_ region: Range<SourceFile.Index>, in source: SourceFile) {
    self.source = source
    self.region = region
  }

  /// The start of the region that `self` represents.
  public var start: SourcePosition { .init(region.lowerBound, in: source) }

  /// The "past-the-end" position of the region that `self` represents.
  public var end: SourcePosition { .init(region.upperBound, in: source) }

  /// The source text covered by this span.
  public var text: Substring { source.text[region] }

  /// Returns a copy of `self` extended to cover `other`.
  public func extended(toCover other: SourceSpan) -> SourceSpan {
    precondition(self.source == other.source, "incompatible spans")
    let l = Swift.min(self.region.lowerBound, other.region.lowerBound)
    let h = Swift.max(self.region.upperBound, other.region.upperBound)
    return .init(.init(uncheckedBounds: (l, h)), in: source)
  }

  /// Returns a copy of `self` with the end increased (if necessary) to `newEnd`.
  public func extended(upTo newEnd: SourceFile.Index) -> SourceSpan {
    let h = Swift.max(self.region.upperBound, newEnd)
    return .init(.init(uncheckedBounds: (self.region.lowerBound, h)), in: source)
  }

  /// Creates an empty span that starts at `p`.
  public static func empty(at p: SourcePosition) -> Self {
    SourceSpan(p.index ..< p.index, in: p.source)
  }

}

extension SourceSpan: CustomStringConvertible {

  /// Returns a textual representation of `self` per the
  /// [GNU coding standards](https://www.gnu.org/prep/standards/html_node/Errors.html) whose path
  /// is shown as `pathStyle`.
  public func gnuStandardText(showingPath pathStyle: FileName.PathStyle = .absolute) -> String {
    let n: String = if case .relative(let u) = pathStyle {
      source.name.gnuPath(relativeTo: u) ?? source.name.description
    } else {
      source.name.description
    }

    let s = start.lineAndColumn
    let h = "\(n):\(s.line).\(s.column)"
    if region.isEmpty { return h }

    let e = end.lineAndColumn
    if e.line == s.line {
      return h + "-\(e.column)"
    } else {
      return h + "-\(e.line):\(e.column)"
    }
  }

  public var description: String {
    gnuStandardText()
  }

}

extension SourceSpan: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    let i = try Int(archive.readUnsignedLEB128())
    let s = (context as! Module.SerializationContext).sources.values[i].source

    let l = try String.Index(utf16Offset: archive.read(Int.self), in: s.text)
    let u = try String.Index(utf16Offset: archive.read(Int.self), in: s.text)
    self.init(l ..< u, in: s)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try modify(&context, as: Module.SerializationContext.self) { (ctx) in
      let i = ctx.sources.index(forKey: source.name)!
      archive.write(unsignedLEB128: i)

      let contents = ctx.sources[source.name]!.source.text
      try archive.write(region.lowerBound.utf16Offset(in: contents))
      try archive.write(region.upperBound.utf16Offset(in: contents))
    }
  }

}
