import Foundation

/// A handle to the standard error.
internal struct StandardError: TextOutputStream, Sendable {

  internal mutating func write(_ string: String) {
    for byte in string.utf8 { putc(numericCast(byte), stderr) }
  }

}
