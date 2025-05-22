import FrontEnd

/// The intermediate representation of a function.
public struct IRFunction {

  /// The name of the function.
  public let identifier: String

  /// The type of the function.
  public let type: AnyTypeIdentity

  /// The signature of the function.
  public let declaration: FunctionDeclaration.ID

  /// The body of the function, if defined.
  public internal(set) var body: IRTree?

}
