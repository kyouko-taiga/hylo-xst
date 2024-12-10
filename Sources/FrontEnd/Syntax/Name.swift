import Archivist
import Utilities

/// An operator notation.
public enum OperatorNotation: UInt8 {

  /// No notation.
  case none = 0

  /// The infix notation.
  case infix = 1

  /// The prefix notation.
  case prefix = 2

  /// The postfix notation.
  case postfix = 3

}

/// The argument labels of a name.
public struct ArgumentLabels {

  /// The value of each label.
  public let values: [String?]

  /// Creates an instance with `values`.
  public init<S: Sequence<String?>>(_ values: S) {
    self.values = .init(values)
  }

}

extension ArgumentLabels: Hashable {}

extension ArgumentLabels: RandomAccessCollection {

  public typealias Element = String?

  public typealias Index = Array<String?>.Index

  public var startIndex: Index { values.startIndex }

  public var endIndex: Index { values.endIndex }

  public func index(after i: Index) -> Index { values.index(after: i) }

  public func index(before i: Index) -> Index { values.index(before: i) }

  public subscript(i: Index) -> Element { values[i] }

}

extension ArgumentLabels: ExpressibleByArrayLiteral {

  public init(arrayLiteral elements: String?...) {
    self.init(elements)
  }

}

extension ArgumentLabels: CustomStringConvertible {

  public var description: String { values.map({ "\($0 ?? "_"):" }).joined() }

}

/// An unqualified name denoting an entity.
public struct Name: Hashable {

  /// The identifier of the referred entity.
  public let identifier: String

  /// The argument labels of the referred entity, given that it is a function.
  public let labels: ArgumentLabels

  /// The operator notation of the referred entity, given that it is an operator.
  public let notation: OperatorNotation

  /// The method introducer of the referred entity, given that it is a method implementation.
  ///
  /// The introducer, if any, is incorporated during parsing, after the original `Name` is created.
  public let introducer: AccessEffect?

  /// Creates an instance with the given properties.
  public init(
    identifier: String,
    labels: ArgumentLabels = [],
    notation: OperatorNotation = .none,
    introducer: AccessEffect? = nil
  ) {
    self.identifier = identifier
    self.labels = labels
    self.notation = notation
    self.introducer = introducer
  }

  /// Returns `self` appending `x` or `nil` if `self` already has an introducer.
  public func appending(_ x: AccessEffect) -> Name? {
    introducer == nil
      ? Name(identifier: identifier, labels: labels, notation: notation, introducer: x)
      : nil
  }

  /// Returns `self` sans access effect.
  public func removingIntroducer() -> Name {
    Name(identifier: identifier, labels: labels, notation: notation)
  }

}

extension Name: CustomStringConvertible {

  public var description: String {
    if notation != .none {
      return "\(notation)\(identifier)"
    } else if labels.isEmpty {
      let introducer = introducer.map({ ".\($0)" }) ?? ""
      return identifier + introducer
    } else {
      let introducer = introducer.map({ ".\($0)" }) ?? ""
      return "\(identifier)(\(labels))" + introducer
    }
  }

}

extension OperatorNotation: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self = try archive.read(rawValueOf: Self.self).unwrapOrThrow(ArchiveError.invalidInput)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(rawValueOf: self)
  }

}

extension Name: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.identifier = try archive.read(String.self)
    self.labels = try ArgumentLabels(archive.read([String].self))
    self.notation = try archive.read(OperatorNotation.self)
    self.introducer = try archive.read(AccessEffect?.self)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try archive.write(identifier)
    try archive.write(labels.values)
    try archive.write(notation)
    try archive.write(introducer)
  }

}
