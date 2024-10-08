import DequeModule
import MoreCollections

/// The type inference and checking algorithm of Hylo programs.
public struct Typer {

  /// The module being typed.
  public let module: Program.ModuleIdentity

  /// The program containing the module being typed.
  private var program: Program

  /// Creates an instance assigning types to syntax trees in `m`, which is a module in `p`.
  public init(typing m: Program.ModuleIdentity, in p: consuming Program) {
    self.module = m
    self.program = p
  }

  /// Type checks the top-level declarations of `self.module`.
  public mutating func apply() {
    for s in program[module].sources.values {
      for d in s.topLevelDeclarations { check(d) }
    }
  }

  /// Returns the resources held by this instance.
  public consuming func release() -> Program {
    self.program
  }

  // MARK: Type checking

  /// Type checks `d`.
  private mutating func check(_ d: DeclarationIdentity) {
    switch program.kind(of: d) {
    case AssociatedTypeDeclaration.self:
      check(program.cast(d, to: AssociatedTypeDeclaration.self)!)
    case FunctionDeclaration.self:
      check(program.cast(d, to: FunctionDeclaration.self)!)
    case TraitDeclaration.self:
      check(program.cast(d, to: TraitDeclaration.self)!)
    default:
      program.unexpected(d)
    }
  }

  /// Type checks `d`.
  private mutating func check(_ d: AssociatedTypeDeclaration.ID) {
    _ = declaredType(of: d)
    // TODO
  }

  /// Type checks `d`.
  private mutating func check(_ d: FunctionDeclaration.ID) {
    _ = declaredType(of: d)
    // TODO
  }

  /// Type checks `d`.
  private mutating func check(_ d: TraitDeclaration.ID) {
    _ = declaredType(of: d)
    // TODO
  }

  /// Returns the declared type of `d` without type checking its contents.
  private mutating func declaredType(of d: DeclarationIdentity) -> AnyTypeIdentity {
    if let t = program[module].type(assignedTo: d) {
      // Type is already in cache.
      return t
    }

    switch program.kind(of: d) {
    case AssociatedTypeDeclaration.self:
      return declaredType(of: program.cast(d, to: AssociatedTypeDeclaration.self)!)
    case TraitDeclaration.self:
      return declaredType(of: program.cast(d, to: AssociatedTypeDeclaration.self)!)
    default:
      program.unexpected(d)
    }
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: AssociatedTypeDeclaration.ID) -> AnyTypeIdentity {
    let p = program.parent(containing: d, as: TraitDeclaration.self)!
    let q = demand(Trait(declaration: p))^
    let t = demand(AssociatedType(declaration: d, qualification: q))^
    let u = demand(Metatype(instance: t))^
    program[module].setType(u, for: d)
    return u
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: FunctionDeclaration.ID) -> AnyTypeIdentity {
    fatalError()
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declatedType(of d: ParameterDeclaration.ID) -> AnyTypeIdentity {
    fatalError()
  }

  /// Returns the declared type of `d` without checking.
  private mutating func declaredType(of d: TraitDeclaration.ID) -> AnyTypeIdentity {
    let t = demand(Trait(declaration: d))^
    let u = demand(Metatype(instance: t))^
    program[module].setType(u, for: d)
    return u
  }

  // MARK: Helpers

  /// Returns the unique identity of a tree that is equal to `t`.
  private mutating func demand<T: TypeTree>(_ t: T) -> T.ID {
    program.types.demand(t)
  }

}
