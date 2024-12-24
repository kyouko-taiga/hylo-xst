/// A declaration that introduces a type entity.
public protocol TypeDeclaration: Declaration {

  /// The identifier of the type introduced by the declaration.
  var identifier: Parsed<String> { get }

}
