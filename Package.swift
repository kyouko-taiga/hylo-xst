// swift-tools-version:5.10
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
      from: "0.4.0"),
    .package(
      url: "https://github.com/apple/swift-argument-parser.git",
      from: "1.1.4"),
    .package(
      url: "https://github.com/apple/swift-algorithms.git",
      from: "1.2.0"),
    .package(
      url: "https://github.com/apple/swift-collections.git",
      from: "1.1.0"),
  ],
  targets: [
    .executableTarget(
      name: "hc",
      dependencies: [
        .target(name: "FrontEnd"),
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
    
    .target(name: "Utilities"),

    .testTarget(
      name: "CompilerTests",
      dependencies: [
        .target(name: "FrontEnd"),
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
