import FrontEnd

/// An error that occurred during compilation.
public struct CompilationError: Error {

  /// The diagnostics of the error.
  public let diagnostics: DiagnosticSet

}
