import FrontEnd

extension FrontEnd.Program {

  /// Returns the name of the C++ type corresponding to `t`.
  internal func cpp(_ t: MachineType.ID) -> String {
    switch types[t] {
    case .i(1):
      return "std::int8_t"
    case .i(32):
      return "std::uint32_t"
    case .i(64):
      return "std::uint64_t"
    default:
      fatalError("unsupported type '\(show(t))'")
    }
  }

}
