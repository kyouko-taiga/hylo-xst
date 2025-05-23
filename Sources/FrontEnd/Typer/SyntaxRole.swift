/// The grammatical role a syntax tree plays.
internal enum SyntaxRole: Equatable {

  /// The tree is used in an unspecified way.
  case unspecified

  /// The tree denotes a type ascription.
  case ascription

  /// The tree denotes as the callee of a function call.
  case function(labels: [String?])

  /// The tree denotes as the callee of a subscript call.
  case `subscript`(labels: [String?])

  /// Creates the role of a callee applied with given `style` and `labels`.
  internal init(_ style: Call.Style, labels: [String?]) {
    switch style {
    case .parenthesized:
      self = .function(labels: labels)
    case .bracketed:
      self = .subscript(labels: labels)
    }
  }

}
