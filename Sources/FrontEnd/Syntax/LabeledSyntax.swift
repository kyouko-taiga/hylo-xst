/// An abstract syntax tree with an optional label.
public protocol LabeledSyntax {

  associatedtype Value: SyntaxIdentity

  /// Creates an instance with the given properties.
  init(label: Parsed<String>?, value: Value)

}
