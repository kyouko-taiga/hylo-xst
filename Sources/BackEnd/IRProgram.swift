import FrontEnd
import OrderedCollections
import Runtime
import Utilities

/// The intermediate representation of a program.
public struct IRProgram {

  /// The repository of type metadata.
  public let store: TypeMetadataStore

  /// The functions in the program.
  public private(set) var functions: OrderedDictionary<String, IRFunction>

  /// The cache of `identifier(of:using:)`
  private var declarationToIdentifier: [DeclarationIdentity: String]

  /// The cache of `fieldIndex(of:using:)`.
  private var fieldToIndex: [VariableDeclaration.ID: Int]

  /// The suffix of the next fresh identifier.
  private var nextSuffix: Int

  /// Creates an empty instance.
  public init() {
    self.store = .init()
    self.functions = [:]
    self.declarationToIdentifier = [:]
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
    return declare(function: n, of: p.type(assignedTo: d)!, notionallyDeclaredBy: d, using: p)
  }

  /// Declares a function named `n`, declared by `d`, and having type `t`.
  public mutating func declare(
    function n: String, of t: AnyTypeIdentity, notionallyDeclaredBy d: FunctionDeclaration.ID,
    using p: FrontEnd.Program
  ) -> String {
    modify(&functions[n]) { (function) in
      if let f = function {
        assert((f.declaration == d) && (f.type == t))
      } else {
        function = .init(identifier: n, type: t.erased, declaration: d)
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
      let m = p.name(of: d).map(\.identifier) ?? p.tag(of: d).description
      let n = "x\(m)\(String(d.erased.bits, radix: 36))"
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
