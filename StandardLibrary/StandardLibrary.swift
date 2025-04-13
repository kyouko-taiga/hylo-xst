import Foundation

/// The root folder of the standard library's sources.
public let standardLibrarySources = URL(fileURLWithPath: #filePath)
  .deletingLastPathComponent()
  .appendingPathComponent("Sources")
