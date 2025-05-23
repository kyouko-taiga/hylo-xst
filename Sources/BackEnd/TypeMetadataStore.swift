import FrontEnd
import Runtime

/// A repository of type metadata.
public class TypeMetadataStore {

  /// A reference to the value of this instance.
  internal let this: Runtime.XSTTypeStoreReference

  /// Creates a new instance of the runtime store.
  internal init() { self.this = Runtime.xst_create_store() }

  /// Disposes of the instance.
  deinit { Runtime.xst_dispose_store(this) }

  /// Returns the size of `t`.
  public func size(of t: TypeMetadata) -> Int {
    Runtime.xst_size(this, t.this)
  }

  /// Returns the alignment of `t`.
  public func alignment(of t: TypeMetadata) -> Int {
    Runtime.xst_alignment(this, t.this)
  }

  /// Returns the metadata of `t`.
  public func metadata(
    of t: AnyTypeIdentity, appliedTo a: TypeArguments,
    using program: inout FrontEnd.Program
  ) -> TypeMetadata {
    switch program.types.tag(of: t) {
    case MachineType.self:
      let u = program.types.castUnchecked(t, to: MachineType.self)
      return metadata(of: u, using: program)

    case Struct.self:
      let u = program.types.castUnchecked(t, to: Struct.self)
      return metadata(of: u, appliedTo: a, using: &program)

    case Tuple.self:
      let u = program.types.castUnchecked(t, to: Tuple.self)
      return metadata(of: u, using: &program)

    case TypeApplication.self:
      let u = program.types[t] as! TypeApplication
      return metadata(of: u.abstraction, appliedTo: u.arguments, using: &program)

    default:
      fatalError("unsupported type '\(program.show(t))'")
    }
  }

  /// Returns the metadata of `t`.
  private func metadata(of t: MachineType.ID, using program: FrontEnd.Program) -> TypeMetadata {
    switch program.types[t] {
    case .i(1):
      return .init(Runtime.xst_declare_builtin(this, XSTBuiltinTagI1))
    case .i(32):
      return .init(Runtime.xst_declare_builtin(this, XSTBuiltinTagI32))
    case .i(64):
      return .init(Runtime.xst_declare_builtin(this, XSTBuiltinTagI64))
    case .ptr:
      return .init(Runtime.xst_declare_builtin(this, XSTBuiltinTagPointer))
    default:
      fatalError("unsupported type '\(program.show(t))'")
    }
  }

  /// Returns the metadata of `t` applied to `a`.
  private func metadata(
    of t: Struct.ID, appliedTo a: TypeArguments = .init(), using program: inout FrontEnd.Program
  ) -> TypeMetadata {
    // Declare the struct.
    let m = declare(t, appliedTo: a, using: &program)
    if isDefined(m) { return m }

    // Enumerate the fields (i.e., stored properties) of the type, in the order of declaration.
    let d = program.types[t].declaration
    let fields = program.storedProperties(of: d)

    // Empty struct?
    if fields.isEmpty {
      Runtime.xst_define_struct(this, m.this, nil, 0)
      return m
    }

    // Define the struct.
    var fs: [XSTField] = []
    for i in 0 ..< fields.count {
      let f = fields[i]
      var u = program.typeSansEffect(assignedTo: f)
      u = (program.types[u] as? RemoteType).map(\.projectee) ?? u
      u = program.types.substitute(a, in: u)

      if program.isIndirect(f) {
        fs.append(
          Runtime.xst_create_field(declare(u, appliedTo: .init(), using: &program).this, 1))
      } else {
        fs.append(
          Runtime.xst_create_field(metadata(of: u, appliedTo: .init(), using: &program).this, 0))
      }
    }

    Runtime.xst_define_struct(this, m.this, &fs, fs.count)
    return m
  }

  /// Returns the metadata of `t` applied to `a`.
  private func metadata(of t: Tuple.ID, using program: inout FrontEnd.Program) -> TypeMetadata {
    // Declare a struct representing the tuple.
    let m = declare(t, using: &program)
    if isDefined(m) { return m }

    // Define the struct.
    var fs = program.types[t].elements.map { (e) in
      Runtime.xst_create_field(declare(e.type, appliedTo: .init(), using: &program).this, 0)
    }
    Runtime.xst_define_struct(this, m.this, &fs, fs.count)
    return m
  }

  /// Declares the application of `t` to the type arguments in `a`.
  public func declare(
    _ t: AnyTypeIdentity, appliedTo a: TypeArguments, using program: inout FrontEnd.Program
  ) -> TypeMetadata {
    switch program.types.tag(of: t) {
    case MachineType.self:
      let u = program.types.castUnchecked(t, to: MachineType.self)
      return metadata(of: u, using: program)

    case Struct.self:
      let u = program.types.castUnchecked(t, to: Struct.self)
      return declare(u, appliedTo: a, using: &program)

    case TypeApplication.self:
      let u = program.types[t] as! TypeApplication
      return declare(u.abstraction, appliedTo: u.arguments, using: &program)

    default:
      fatalError("unsupported type '\(program.show(t))'")
    }
  }

  /// Declares the application of `t` to the type arguments in `a`.
  private func declare(
    _ t: Struct.ID, appliedTo a: TypeArguments, using program: inout FrontEnd.Program
  ) -> TypeMetadata {
    var arguments: [XSTTypeHeaderReference?] = a.values.map { (u) in
      metadata(of: u, appliedTo: .init(), using: &program).this
    }
    let d = program.types[t].declaration
    return program[d].identifier.value.withCString { (n) in
      TypeMetadata(Runtime.xst_declare_struct(this, n, &arguments, arguments.count))
    }
  }


  /// Declares `t`.
  private func declare(_ t: Tuple.ID, using program: inout FrontEnd.Program) -> TypeMetadata {
    program.show(t).withCString { (n) in
      TypeMetadata(Runtime.xst_declare_struct(this, n, nil, 0))
    }
  }

  /// Returns `true` iff `t` has a definition.
  private func isDefined(_ t: TypeMetadata) -> Bool {
    Runtime.xst_is_defined(this, t.this) != 0
  }

}

/// Information about a type at runtime.
public struct TypeMetadata {

  /// A reference to the value of this instance.
  internal let this: Runtime.XSTTypeHeaderReference

  /// Creates an instance wrapping the given reference.
  internal init(_ this: Runtime.XSTTypeHeaderReference) {
    self.this = this
  }

}
