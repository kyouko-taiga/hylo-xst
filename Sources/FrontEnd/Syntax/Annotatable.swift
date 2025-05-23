/// A syntax tree that may have annotations.
public protocol Annotatable: Syntax {

  /// The annotations on this node.
  var annotations: [Annotation] { get }

}
