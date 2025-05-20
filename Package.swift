// swift-tools-version:6.0
import PackageDescription

#if os(Windows)
  let onWindows = true
#else
  let onWindows = false
#endif

let package = Package(
  name: "Hylo",
  platforms: [
    .macOS(.v13)
  ],
  products: [
    .executable(name: "hc", targets: ["hc"])
  ],
  dependencies: [
    .package(
      url: "https://github.com/kyouko-taiga/archivist.git",
      branch: "main"),
    .package(
      url: "https://github.com/kyouko-taiga/more-swift-collections.git",
      from: "0.6.1"),
    .package(
      url: "https://github.com/apple/swift-algorithms.git",
      from: "1.2.0"),
    .package(
      url: "https://github.com/apple/swift-argument-parser.git",
      from: "1.1.4"),
    .package(
      url: "https://github.com/apple/swift-collections.git",
      from: "1.1.0"),
  ],
  targets: [
    .executableTarget(
      name: "hc",
      dependencies: [
        .target(name: "Driver"),
        .target(name: "FrontEnd"),
        .target(name: "Utilities"),
        .product(name: "ArgumentParser", package: "swift-argument-parser"),
      ]),

    .target(
      name: "BackEnd",
      dependencies: [
        .target(name: "Utilities"),
        .target(name: "FrontEnd"),
        .product(name: "Algorithms", package: "swift-algorithms"),
        .product(name: "Collections", package: "swift-collections"),
      ]),

    .target(
      name: "Driver",
      dependencies: [
        .target(name: "BackEnd"),
        .target(name: "FrontEnd"),
        .target(name: "StandardLibrary"),
        .target(name: "Utilities"),
        .product(name: "Archivist", package: "archivist"),
      ]),

    .target(
      name: "FrontEnd",
      dependencies: [
        .target(name: "Utilities"),
        .product(name: "Archivist", package: "archivist"),
        .product(name: "Algorithms", package: "swift-algorithms"),
        .product(name: "Collections", package: "swift-collections"),
        .product(name: "MoreCollections", package: "more-swift-collections")
      ]),

    .target(
      name: "StandardLibrary",
      // dependencies: ["FrontEnd", "Utils"],
      path: "StandardLibrary",
      resources: [.copy("Sources")]),

    .target(
      name: "Utilities",
      dependencies: [
        .product(name: "Algorithms", package: "swift-algorithms"),
      ]),

    .testTarget(
      name: "CompilerTests",
      dependencies: [
        .target(name: "Driver"),
        .target(name: "FrontEnd"),
        .target(name: "Utilities"),
      ],
      exclude: ["negative", "positive"]),

    .testTarget(
      name: "FrontEndTests",
      dependencies: [
        .target(name: "FrontEnd"),
      ]),

    .testTarget(
      name: "UtilitiesTests",
      dependencies: [
        .target(name: "Utilities"),
      ]),
  ])
