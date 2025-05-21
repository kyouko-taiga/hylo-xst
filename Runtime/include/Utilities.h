#pragma once

#include <cstdint>
#include <numeric>
#include <sstream>
#include <type_traits>
#include <utility>

namespace xst {

// --- Error reporting ----------------------------------------------------------------------------

/// Ensures that the given condition is satisfied or throws an error.
void precondition(bool test, std::string const& error);

// --- Functions on binary integers ---------------------------------------------------------------

/// Returns `a` rounded up to the nearest multiple of `b`.
template<typename Integer>
constexpr Integer round_up_to_nearest_multiple(Integer const& a, Integer const& b) {
  auto r = a % b;
  if (r == 0) {
    return a;
  } else if (a < 0) {
    return a - r;
  } else {
    return a + (b - r);
  }
}

/// Returns an instance with the bit representation of `source`, truncating or sign-extending it
/// to fit the bit representation of an `std::size_t`.
template<typename S, typename T>
constexpr T truncate_or_extend(S source) {
  T result = (std::is_signed<S>::value && source < 0) ? std::numeric_limits<T>::max() : 0;
  memcpy(&result, &source, std::min(sizeof(S), sizeof(T)));
  return result;
}

// --- Memory -------------------------------------------------------------------------------------

/// Returns `base_address` advanced by `offset`.
inline constexpr void* advance(void* base_address, std::size_t offset) {
  return static_cast<void*>(static_cast<std::byte*>(base_address) + offset);
}

/// Returns `base_address` advanced by the offset necessary to form a pointer aligned by the
/// specified `alignemnt` alignment.
inline constexpr void* align(void* base_address, std::size_t alignment) {
  auto x = reinterpret_cast<std::uintptr_t>(base_address);
  auto y = round_up_to_nearest_multiple(x, alignment);
  return reinterpret_cast<std::byte*>(y);
}

template<std::size_t size, std::size_t alignment>
struct AlignedBuffer {
private:
  std::byte memory[size + alignment - 1];

public:
  AlignedBuffer() : memory{} {}

  inline constexpr std::byte* base_address() const {
    auto x = reinterpret_cast<std::uintptr_t>(&memory);
    auto y = round_up_to_nearest_multiple(x, alignment);
    return reinterpret_cast<std::byte*>(y);
  }

};

/// Allocates `s` bytes of storage aligned `a`, initialized to 0 iff `zero_initialize` is set.
void* aligned_alloc(std::size_t a, std::size_t s, bool zero_initialize = false);

/// Deallocates memory allocated by `aligned_alloc`.
///
/// This function is a no-op if `p` is `nullptr`.
void aligned_free(void* p);

// --- Hashing ------------------------------------------------------------------------------------

/// A utility for hashing contents.
struct Hasher {

  static constexpr int64_t basis = 0xcbf29ce484222325;
  static constexpr int64_t prime = 0x100000001b3;

  /// The current state of the hasher.
  int64_t state;

  /// Creates a new instance.
  constexpr Hasher() : state(basis) {}

  /// Combines a hash of `contents` into the state of this hasher.
  template<typename T, typename Hash = std::hash<T>>
  constexpr void combine(T const& contents) {
    std::size_t h = Hash{}(contents);
    for (auto i = 0; i < sizeof(std::size_t); ++i) {
      state = state * Hasher::prime;
      state = state ^ (h & 0xff);
      h = h >> 8;
    }
  }

  /// Combines a hash of `contents` into the state of this hasher.
  template<
  typename Iterator,
  typename Hash = std::hash<typename std::iterator_traits<Iterator>::value_type>
  >
  constexpr void combine(Iterator first, Iterator last) {
    auto i = first;
    while (i != last) {
      combine<typename std::iterator_traits<Iterator>::value_type, Hash>(*i);
      ++i;
    }
  }

  /// Returns the final value of the hasher.
  constexpr std::size_t finalize() {
    return truncate_or_extend<int64_t, std::size_t>(state);
  }

};

/// A utility using dereferenced values in a hashed container indexed by pointers.
template<typename T, typename Hash = std::hash<T>, typename Equal = std::equal_to<T>>
struct DereferencingKey {

  /// A pointer to the value of the key.
  T const* value;

};

}


template<typename T, typename H, typename E>
struct std::hash<xst::DereferencingKey<T, H, E>> {

  constexpr std::size_t operator()(xst::DereferencingKey<T, H, E> const& k) const {
    return H{}(*(k.value));
  }

};

template<typename T, typename H, typename E>
struct std::equal_to<xst::DereferencingKey<T, H, E>> {

  constexpr bool operator()(
    const xst::DereferencingKey<T, H, E>& lhs,
    const xst::DereferencingKey<T, H, E>& rhs
  ) const {
    return (lhs.value == rhs.value) || E{}(*(lhs.value), *(rhs.value));
  }

};
