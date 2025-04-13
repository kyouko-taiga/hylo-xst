import Archivist
import OrderedCollections
import Utilities

/// The application of a type abstraction.
public struct TypeApplication: TypeTree {

  /// The arguments of a type application.
  public typealias Arguments = OrderedDictionary<GenericParameter.ID, AnyTypeIdentity>

  /// The abstraction being applied.
  public var abstraction: AnyTypeIdentity

  /// The arguments of the application.
  public var arguments: Arguments

  /// Properties about `self`.
  public var properties: ValueProperties {
    arguments.values.reduce(abstraction.properties, { (a, i) in a.union(i.properties) })
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> TypeApplication {
    let t = store.map(abstraction, transform)
    let x = arguments.mapValues({ (a) in store.map(a, transform) })
    return .init(abstraction: t, arguments: x)
  }

  /// Returns a table mapping each parameter in `ps` to its corresponding argument in `ts`.
  public static func arguments<P: Collection, A: Collection>(
    mapping ps: P, to ts: A
  ) -> Arguments where P.Element == GenericParameter.ID, A.Element == AnyTypeIdentity {
    assert(ps.count == ts.count)
    var ss = Arguments(minimumCapacity: ps.count)
    for (p, t) in zip(ps, ts) {
      ss[p] = t
    }
    return ss
  }

  /// Returns an argument table read from `archive`.
  public static func arguments<T>(
    from archive: inout ReadableArchive<T>, in context: inout Any
  ) throws -> Arguments {
    let count = try Int(archive.readUnsignedLEB128())
    var result = Arguments(minimumCapacity: count)
    for _ in 0 ..< count {
      let k = try archive.read(GenericParameter.ID.self, in: &context)
      let v = try archive.read(AnyTypeIdentity.self, in: &context)
      result[k] = v
    }
    return result
  }

}

extension TypeApplication: Showable {

  /// Returns a textual representation of `self` using `printer`.
  public func show(using printer: inout TreePrinter) -> String {
    "\(printer.show(abstraction))<\(printer.show(arguments.values))>"
  }

}

extension TypeApplication: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self.abstraction = try archive.read(AnyTypeIdentity.self, in: &context)
    self.arguments = try TypeApplication.arguments(from: &archive, in: &context)
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    try abstraction.write(to: &archive, in: &context)
    try arguments.elements.write(to: &archive) { (e, a) in
      try e.key.write(to: &a, in: &context)
      try e.value.write(to: &a, in: &context)
    }
  }

}
