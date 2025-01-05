import Utilities

/// The application of a type abstraction.
public struct TypeApplication: TypeTree {

  /// The abstraction being applied.
  public var abstraction: AnyTypeIdentity

  /// The arguments of the application.
  public var arguments: [Value]

  /// Properties about `self`.
  public var properties: ValueProperties {
    arguments.reduce(abstraction.properties, { (a, i) in a.union(i.properties) })
  }

  /// Returns `self`, which is in `store`, with its parts transformed by `transform(_:_:)`.
  public func modified(
    in store: inout TypeStore,
    by transform: (inout TypeStore, AnyTypeIdentity) -> TypeTransformAction
  ) -> TypeApplication {
    let t = store.map(abstraction, transform)
    let x: [Value] = arguments.map { (a) in
      a.type.map({ (t) in .type(store.map(t, transform)) }) ?? a
    }
    return .init(abstraction: t, arguments: x)
  }

  /// Returns a parsable representation of `self`, which is a type in `program`.
  public func show(readingChildrenFrom program: Program) -> String {
    "\(program.show(abstraction))<\(list: arguments.map(program.show(_:)))>"
  }

}
