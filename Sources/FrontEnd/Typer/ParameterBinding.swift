/// Information identifying a run-time argument of a function or subscript call.
internal enum ParameterBinding {

  /// The argument is the n-th expression in the syntax of the call.
  case explicit(Int)

  /// The argument is a an implicit declaration reference.
  case implicit(DeclarationReference)

  /// The argument is elided; the callee receive the parameter's default value.
  case defaulted

}
