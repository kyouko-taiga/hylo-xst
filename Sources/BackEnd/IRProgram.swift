import FrontEnd
import OrderedCollections
import Utilities

/// The intermediate representation of a program.
public struct IRProgram {

  /// The functions in the program.
  public private(set) var functions: OrderedDictionary<String, IRFunction>

  /// The cache of `identifier(of:using:)`
  private var declarationToIdentifier: [DeclarationIdentity: String]

  /// The cache of `metatype(of:using:)`
  private var typeToMetatype: [AnyTypeIdentity: Metatype]

  /// The cache of `fieldIndex(of:using:)`.
  private var fieldToIndex: [VariableDeclaration.ID: Int]

  /// The suffix of the next fresh identifier.
  private var nextSuffix: Int

  /// Creates an empty instance.
  public init() {
    self.functions = [:]
    self.declarationToIdentifier = [:]
    self.typeToMetatype = [:]
    self.fieldToIndex = [:]
    self.nextSuffix = 1 // suffix 0 is for result storage
  }

  /// Returns a fresh IR identifier.
  public mutating func fresh() -> String {
    defer { nextSuffix += 1 }
    return "x\(nextSuffix)"
  }

  /// Declares a `d`.
  public mutating func declare(
    function d: FunctionDeclaration.ID, using p: FrontEnd.Program
  ) -> String {
    let n = identifier(of: d, using: p)
    modify(&functions[n]) { (function) in
      if let f = function {
        assert(f.declaration == d)
      } else {
        function = .init(identifier: n, declaration: d)
      }
    }
    return n
  }

  /// Defines the body of the function `n`.
  public mutating func define(function n: String, body: IRTree) {
    functions[n]!.body = body.normalized
  }

  /// Returns the IR identifier of `d`.
  public mutating func identifier<T: Declaration>(
    of d: T.ID, using p: FrontEnd.Program
  ) -> String {
    identifier(of: DeclarationIdentity(d), using: p)
  }

  /// Returns the IR identifier of `d`.
  public mutating func identifier(
    of d: DeclarationIdentity, using p: FrontEnd.Program
  ) -> String {
    if let n = declarationToIdentifier[d] {
      return n
    } else {
      let n = "x" + p.nameOrTag(of: d) + String(d.erased.bits, radix: 36)
      declarationToIdentifier[d] = n
      return n
    }
  }

  /// Returns the type assigned to `n` ignoring projections.
  public func type<T: SyntaxIdentity>(
    assignedTo n: T, using p: FrontEnd.Program
  ) -> AnyTypeIdentity {
    let t = p.typeSansEffect(assignedTo: n)
    return (p.types[t] as? RemoteType).map(\.projectee) ?? t
  }

  /// Returns the metatype of `t`.
  public mutating func metatype(of t: AnyTypeIdentity, using p: FrontEnd.Program) -> Metatype {
    switch p.types.tag(of: t) {
    case MachineType.self:
      return metatype(of: p.types.castUnchecked(t, to: MachineType.self), using: p)
    case Struct.self:
      return metatype(of: p.types.castUnchecked(t, to: Struct.self), using: p)
    default:
      fatalError("unsupported type '\(p.show(t))'")
    }
  }

  /// Returns the metatype of `t`.
  ///
  /// This method assumes that a pointer fits a 64-bit integer on the target machine.
  public mutating func metatype(of t: MachineType.ID, using p: FrontEnd.Program) -> Metatype {
    if let m = typeToMetatype[t.erased] { return m }

    let m: Metatype
    switch p.types[t] {
    case .i(1):
      m = .init(type: t.erased, size: 1, alignment: 1, offsets: [], isTrivial: true)
    case .i(32):
      m = .init(type: t.erased, size: 4, alignment: 4, offsets: [], isTrivial: true)
    case .i(64):
      m = .init(type: t.erased, size: 8, alignment: 8, offsets: [], isTrivial: true)
    case .ptr:
      m = .init(type: t.erased, size: 8, alignment: 8, offsets: [], isTrivial: true)
    default:
      fatalError("unsupported type '\(p.show(t))'")
    }

    typeToMetatype[t.erased] = m
    return m
  }

  /// Returns the metatype of `t`.
  public mutating func metatype(of t: Struct.ID, using p: FrontEnd.Program) -> Metatype {
    if let m = typeToMetatype[t.erased] { return m }

    // Enumerate the fields (i.e., stored properties) of the type, in the order of declaration.
    let fields = p.storedProperties(of: p.types[t].declaration)

    // Empty type?
    if fields.isEmpty {
      let m = Metatype(type: t.erased, size: 0, alignment: 1, offsets: [], isTrivial: true)
      typeToMetatype[t.erased] = m
      return m
    }

    // Compute size, alignment, and offset of each field.
    var sizes = [metatype(of: type(assignedTo: fields[0], using: p), using: p).size]
    var offsets = [0]
    var alignment = 1
    var isTrivial = true

    for i in 1 ..< fields.count {
      let f = fields[i]
      let o = offsets[i - 1] + sizes[i - 1]

      // Indirect fields are represented by a pointer to out-of-line storage.
      if p.isIndirect(f) {
        sizes.append(8)
        offsets.append(o.rounded(upToNearestMultipleOf: 8))
        alignment = max(alignment, 8)
        isTrivial = false
      }

      // Other properties are stored inline.
      else {
        let m = metatype(of: type(assignedTo: f, using: p), using: p)
        sizes.append(m.size)
        offsets.append(o.rounded(upToNearestMultipleOf: m.alignment))
        alignment = max(alignment, m.alignment)
      }
    }
    let size = offsets.last! + sizes.last!

    let m = Metatype(
      type: t.erased, size: size, alignment: alignment, offsets: offsets, isTrivial: isTrivial)
    typeToMetatype[t.erased] = m
    return m
  }

  /// Returns the position of the variable `d` in the inline storage of the struct of which it is
  /// a stored property.
  public mutating func fieldIndex(
    of d: VariableDeclaration.ID, using p: FrontEnd.Program
  ) -> Int {
    if let i = fieldToIndex[d] { return i }

    // `d` must be contained in a struct declaration.
    let s = p.parent(containing: d, as: StructDeclaration.self)!
    let i = p.storedProperties(of: s).firstIndex(of: d)!
    fieldToIndex[d] = i
    return i
  }

}

extension IRProgram: Showable {

  public func show(using printer: inout TreePrinter) -> String {
    var result = ""
    for f in functions.values {
      result.write(f.identifier)
      if let body = f.body {
        result.write(" =\n  \(printer.show(body))")
      }
      result.write(";\n")
    }
    return result
  }

}

extension FrontEnd.Program {

  /// Returns the type assigned to `n` ignoring projections.
  public func typeSansEffect<T: SyntaxIdentity>(assignedTo n: T) -> AnyTypeIdentity {
    let t = type(assignedTo: n)!
    return (types[t] as? RemoteType).map(\.projectee) ?? t
  }

}
