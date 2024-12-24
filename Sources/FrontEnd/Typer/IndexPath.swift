/// A list of indices representing the path to a specific location in a tree.
///
/// A path is relative to a tree that is represented as a nested arrays. Given a path `p`, `p[i]`
/// denotes the index of a child in the tree identified by `p[..<i]`. An empty path denotes the
/// root of the tree.
public typealias IndexPath = [Int]
