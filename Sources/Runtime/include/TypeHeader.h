#pragma once

#include "Utilities.h"

#include <sstream>
#include <string>
#include <vector>

namespace xst {

struct TypeHeader;
struct TypeStore;

/// A type-erased function pointer.
///
/// This type is used to compute the size and aligment of function pointers stored in instances of
/// a lambda. It is used instead of `void*` because converting a function pointer to the latter is
/// on defined on posix-compliant systems.
using AnyFunction = void(*)();

/// The information necessary to uniquely identify atype.
struct TypeHeader {

  /// Destorys `this`.
  virtual ~TypeHeader() = default;

  /// Returns a hash of the salient part of `this`.
  virtual std::size_t hash_value() const = 0;

  /// Returns `true` iff `this` is equal to the given identifier.
  virtual bool equal_to(TypeHeader const&) const = 0;

  /// Returns a textual description of the type.
  virtual std::string description() const = 0;

  /// Returns `true` iff `this` is equal to `other`.
  bool operator==(TypeHeader const& other) const {
    return this->equal_to(other);
  }

private:

  // Note: The following methods are notionally methods of the type store and are no meant to be
  // called from anywhere else. They are defined here to enable the default dynamic dispatch
  // mechanism of virtual calls.

  friend TypeStore;

  /// Implements `TypeStore::copy_initialize` for the described type.
  virtual void copy_initialize(void*, void*, TypeStore const&) const = 0;

  /// Implements `TypeStore::deinitialize` for the described type.
  virtual void deinitialize(void*, TypeStore const&) const = 0;

  /// Implements `TypeStore::dump_instance` for the described type.
  virtual void dump_instance(std::ostream&, void*, TypeStore const&) const = 0;

};

/// The header of a built-in type.
struct BuiltinHeader final : public TypeHeader {

  /// The internal representation of a built-in identifier.
  enum Value : uint8_t {
    i1,
    i32,
    i64,
    ptr,
    fun,
  };

  /// The raw value of this identifier.
  Value raw_value;

  /// Creates an instance with the given raw value.
  constexpr BuiltinHeader(Value raw_value) : raw_value(raw_value) {}

  /// Returns the size of an instance of the type.
  constexpr std::size_t size() const {
    switch (raw_value) {
      case i1: return sizeof(std::int8_t);
      case i32: return sizeof(std::int32_t);
      case i64: return sizeof(std::int64_t);
      case ptr: return sizeof(void*);
      case fun: return sizeof(AnyFunction);
    }
  }

  /// Returns the alignment the type.
  constexpr std::size_t alignment() const {
    switch (raw_value) {
      case i1: return alignof(std::int8_t);
      case i32: return alignof(std::int32_t);
      case i64: return alignof(std::int64_t);
      case ptr: return alignof(void*);
      case fun: return alignof(AnyFunction);
    }
  }

  constexpr std::size_t hash_value() const override {
    return static_cast<std::size_t>(raw_value);
  }

  constexpr bool equal_to(TypeHeader const& other) const override {
    auto const* that = dynamic_cast<BuiltinHeader const*>(&other);
    if (that != nullptr) {
      return this->raw_value == that->raw_value;
    } else {
      return false;
    }
  }

  constexpr std::string description() const override {
    switch (raw_value) {
      case i1: return "i1";
      case i32: return "i32";
      case i64: return "i64";
      case ptr: return "ptr";
      case fun: return "fun";
    }
  }

private:

  void copy_initialize(void*, void*, TypeStore const&) const override;

  void deinitialize(void*, TypeStore const&) const override;

  void dump_instance(std::ostream&, void*, TypeStore const&) const override;

};

/// Common implementation of nominal product and sum types.
struct CompositeHeader : public TypeHeader {

  /// The name of the type.
  const std::string name;

  /// The type arguments of the type.
  const std::vector<TypeHeader const*> arguments;

  /// Creates an instance with the given properties.
  constexpr CompositeHeader(
    std::string const& name, std::initializer_list<TypeHeader const*> arguments
  ) : name(name), arguments(arguments) {}

  /// Creates an instance with the given properties.
  template<typename Iterator>
  constexpr CompositeHeader(
    std::string const& name, Iterator first, Iterator last
  ) : name(name), arguments(first, last) {}

  constexpr std::size_t hash_value() const override {
    Hasher h;
    h.combine(name);
    h.combine(arguments.begin(), arguments.end());
    return h.finalize();
  }

  std::string description() const override {
    std::stringstream o;
    o << name;
    if (!arguments.empty()) {
      o << "<";
      auto f = true;
      for (auto a : arguments) {
        if (f) { f = false; } else { o << ", "; }
        o << a->description();
      }
      o << ">";
    }
    return o.str();
  }

};

/// The header of a product type.
struct StructHeader final : public CompositeHeader {

  /// Creates an instance with the given properties.
  constexpr StructHeader(
    std::string const& name, std::initializer_list<TypeHeader const*> arguments
  ) : CompositeHeader(name, arguments) {}

  /// Creates an instance with the given properties.
  template<typename Iterator>
  constexpr StructHeader(
    std::string const& name, Iterator first, Iterator last
  ) : CompositeHeader(name, first, last) {}

  constexpr bool equal_to(TypeHeader const& other) const override {
    auto const* that = dynamic_cast<StructHeader const*>(&other);
    if (that != nullptr) {
      return (this->name == that->name) && (this->arguments == that->arguments);
    } else {
      return false;
    }
  }

private:

  void copy_initialize(void*, void*, TypeStore const&) const override;

  void deinitialize(void*, TypeStore const&) const override;

  void dump_instance(std::ostream&, void*, TypeStore const&) const override;

};

/// The header of a sum type.
struct EnumHeader final : public CompositeHeader {

  /// Creates an instance with the given properties.
  constexpr EnumHeader(
    std::string const& name, std::initializer_list<TypeHeader const*> arguments
  ) : CompositeHeader(name, arguments) {}

  constexpr bool equal_to(TypeHeader const& other) const override {
    auto const* that = dynamic_cast<EnumHeader const*>(&other);
    if (that != nullptr) {
      return (this->name == that->name) && (this->arguments == that->arguments);
    } else {
      return false;
    }
  }

private:

  void copy_initialize(void*, void*, TypeStore const&) const override;

  void deinitialize(void*, TypeStore const&) const override;

  void dump_instance(std::ostream&, void*, TypeStore const&) const override;

};

}

template<>
struct std::hash<xst::TypeHeader> {

  std::size_t operator()(xst::TypeHeader const& i) const {
    return i.hash_value();
  }

};
