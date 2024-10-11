/// A parameter of a callable abstraction.
public struct Parameter: Hashable {

  /// The label of the parameter.
  public let label: String?

  /// The type of the parameter.
  public let type: AnyTypeIdentity

  /// `true` iff the parameter has a default argument.
  public let hasDefault: Bool

  /// `true` if arguments to the parameter can be passed implicitly.
  public let isImplicit: Bool

  /// `true` iff the parameter is implicit or has a default argument.
  public var isElidible: Bool {
    hasDefault || isImplicit
  }

}

extension Program {

  /// Returns a source-like representation of `p`.
  public func show(_ p: Parameter) -> String {
    let t = show(p.type)
    return if let l = p.label { "\(l): \(t)" } else { t }
  }

}
