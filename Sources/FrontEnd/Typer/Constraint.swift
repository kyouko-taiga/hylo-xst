/// An equation involving compile-time values.
internal protocol Constraint {

  /// The site from which the constraint originates.
  var site: SourceSpan { get }

  /// `true` iff `self` trivially holds and solving it will not enable any new deductions.
  var isTrivial: Bool { get }

  /// Applies `transform` on constituent types of `self`.
  mutating func update(_ transform: (AnyTypeIdentity) -> AnyTypeIdentity)

  /// Returns a textual representation of `self`, reading contents from `program`.
  func show(using program: Program) -> String

}

extension Program {

  /// Returns a debug representation of `k`.
  internal func show(_ k: any Constraint) -> String {
    k.show(using: self)
  }

  /// Returns a debug representation of the elements in `ks`.
  internal func show<S: Sequence<any Constraint>>(_ ks: S) -> String {
    ks.map(show(_:)).joined(separator: "\n")
  }

}

/// A constraint stating that two types are equal.
internal struct TypeEquality: Constraint {

  /// The left operand.
  internal private(set) var lhs: AnyTypeIdentity

  /// The right operand.
  internal private(set) var rhs: AnyTypeIdentity

  /// The site from which the constraint originates.
  internal let site: SourceSpan

  /// `true` iff `self` trivially holds and solving it will not enable any new deductions.
  internal var isTrivial: Bool {
    lhs == rhs
  }

  /// Applies `transform` on constituent types of `self`.
  internal mutating func update(_ transform: (AnyTypeIdentity) -> AnyTypeIdentity) {
    lhs = transform(lhs)
    rhs = transform(rhs)
  }

  /// Returns a textual representation of `self`, reading contents from `program`.
  internal func show(using program: Program) -> String {
    program.format("%T == %T", [lhs, rhs])
  }

}

/// A constraint stating that a value of type `F` can be applied to values of types `A1, ..., An`
/// for producing a value of type `R`.
internal struct CallConstraint: Constraint {

  /// The label, type, and site of an argument passed to a callable object.
  internal struct Argument: Hashable {

    /// The label of the argument, if any.
    internal let label: String?

    /// The type of the argument.
    internal var type: AnyTypeIdentity

  }

  /// The type of an entity being applied.
  internal let callee: AnyTypeIdentity

  /// The labels and types of the arguments.
  internal private(set) var arguments: [Argument]

  /// The expected type of the application.
  internal private(set) var output: AnyTypeIdentity

  /// The expression of the application from which the constraint originates.
  internal let origin: Call.ID

  /// The site from which the constraint originates.
  internal let site: SourceSpan

  /// `true` iff `self` trivially holds and solving it will not enable any new deductions.
  internal var isTrivial: Bool {
    false
  }

  /// The expected labels of `callee`.
  internal var labels: some Sequence<String?> {
    arguments.lazy.map(\.label)
  }

  /// Applies `transform` on constituent types of `self`.
  internal mutating func update(_ transform: (AnyTypeIdentity) -> AnyTypeIdentity) {
    for i in 0 ..< arguments.count {
      arguments[i].type = transform(arguments[i].type)
    }
    output = transform(output)
  }

  /// Returns a textual representation of `self`, reading contents from `program`.
  internal func show(using program: Program) -> String {
    var s = program.show(callee)
    // if program.kind(of: origin) == SubscriptCall
    s.write(" applied to (")
    for i in 0 ..< arguments.count {
      if i != 0 { s.write(", ") }
      if let l = arguments[i].label { s.write("\(l): ") }
      s.write(program.show(arguments[i].type))
    }
    s.write(") gives ")
    s.write(program.show(output))
    return s
  }

}

/// A constraint stating that a value of type `A` can be passed to a parameter of type `A`.
internal struct ArgumentConstraint: Constraint {

  /// The type of the argument.
  internal private(set) var lhs: AnyTypeIdentity

  /// The type of the parameter.
  internal private(set) var rhs: AnyTypeIdentity

  /// The site from which the constraint originates.
  internal let site: SourceSpan

  /// `true` iff `self` trivially holds and solving it will not enable any new deductions.
  internal var isTrivial: Bool {
    false
  }

  /// Applies `transform` on constituent types of `self`.
  internal mutating func update(_ transform: (AnyTypeIdentity) -> AnyTypeIdentity) {
    lhs = transform(lhs)
    rhs = transform(rhs)
  }

  /// Returns a textual representation of `self`, reading contents from `program`.
  internal func show(using program: Program) -> String {
    program.format("%T ↓ %T", [lhs, rhs])
  }

}
