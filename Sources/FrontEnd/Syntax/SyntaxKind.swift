import Archivist

/// The type of a node in an abstract syntax tree.
public struct SyntaxKind {

  /// The underlying value of `self`.
  public let value: any Syntax.Type

  /// Creates an instance with the given underlying value.
  public init(_ value: any Syntax.Type) {
    self.value = value
  }

  /// Returns `true` iff `scrutinee` and `pattern` denote the same node type.
  public static func ~= (pattern: any Syntax.Type, scrutinee: Self) -> Bool {
    scrutinee == pattern
  }

  /// Returns `true` iff `l` and `r` denote the same node type.
  public static func == (l: Self, r: any Syntax.Type) -> Bool {
    l.value == r
  }

  /// Returns `true` iff `l` and `r` denote the same node type.
  public static func == (l: Self, r: (any Syntax.Type)?) -> Bool {
    l.value == r
  }

  static let allValues: [any Syntax.Type] = [
    // Declarations
    AssociatedTypeDeclaration.self,
    BindingDeclaration.self,
    ConformanceDeclaration.self,
    ExtensionDeclaration.self,
    FunctionDeclaration.self,
    GenericParameterDeclaration.self,
    ImportDeclaration.self,
    InitializerDeclaration.self,
    ParameterDeclaration.self,
    StructDeclaration.self,
    TraitDeclaration.self,
    TypeAliasDeclaration.self,
    VariableDeclaration.self,

    // Expressions
    BooleanLiteral.self,
    Call.self,
    NameExpression.self,
    RemoteTypeExpression.self,
    SynthethicExpression.self,
    TupleLiteral.self,
    TupleTypeExpression.self,

    // Patterns
    BindingPattern.self,
    TuplePattern.self,

    // Statements
    Discard.self,
    Return.self,
  ]

  static let indices = Dictionary(
    uniqueKeysWithValues: allValues.enumerated().map({ (i, k) in (SyntaxKind(k), i) }))

}

extension SyntaxKind: Equatable {

  public static func == (l: Self, r: Self) -> Bool {
    l.value == r.value
  }

}

extension SyntaxKind: Hashable {

  public func hash(into hasher: inout Hasher) {
    hasher.combine(ObjectIdentifier(value))
  }

}

extension SyntaxKind: Archivable {

  public init<T>(from archive: inout ReadableArchive<T>, in context: inout Any) throws {
    self = try .init(Self.allValues[Int(archive.readUnsignedLEB128())])
  }

  public func write<T>(to archive: inout WriteableArchive<T>, in context: inout Any) throws {
    archive.write(unsignedLEB128: Self.indices[self]!)
  }

}

extension SyntaxKind: CustomStringConvertible {

  public var description: String {
    String(describing: value)
  }

}
