#pragma once

#include "Metatype.h"
#include "TypeHeader.h"
#include "Utilities.h"

#include <algorithm>
#include <unordered_map>

namespace xst {

/// A helper type to initialize metatypes in `TypeStore::declare`.
template<typename Header>
struct MetatypeConstructor {

  /// Constructs a metatype for the given header, using the given store.
  ///
  /// This method is called in `TypeStore::declare` when a new type header is about to be inserted
  /// and it returns a new metatype for that header. The default implementation returns an empty
  /// (i.e., undefined) instance to be defined later by `TypeStore::define`. Specialization of this
  /// method can return a defined metatype so that the instance associated with a header is defined
  /// automatically in `TypeStore::declare`.
  Metatype operator()(Header const*, TypeStore&) {
    return Metatype{};
  }

};

/// A repository of type metadata.
struct TypeStore {
private:

  /// An array containing the type headers allocated in this store.
  std::vector<std::unique_ptr<TypeHeader>> headers;

  /// A table from a type identifier to its corresponding metatype.
  std::unordered_map<DereferencingKey<TypeHeader>, Metatype> metatype;

  /// Returns `t`'s metatype.
  ///
  /// - Requires: `t` has been declared and never explicitly defined in `this`.
  Metatype& get_undefined_metatype(TypeHeader const* t);

public:

  /// Creates an empty instance.
  TypeStore() = default;

  /// Returns a pointer to the unique instance equal to `identifier` in this store.
  template<typename T, typename M = MetatypeConstructor<T>>
  T const* declare(T&& identifier) {
    auto entry = metatype.find(DereferencingKey<TypeHeader>{&identifier});

    // The identifier is already known.
    if (entry != metatype.end()) {
      return static_cast<T const*>(entry->first.value);
    }

    // The identifier is unknown; intern it.
    else {
      headers.emplace_back(std::make_unique<T>(std::move(identifier)));
      auto const* p = headers.back().get();
      auto const* q = static_cast<T const*>(p);
      metatype.emplace(std::make_pair(DereferencingKey{p}, M{}(q, *this)));
      return q;
    }
  }

  /// Returns a pointer to the unique instance identifying `tag` in this store.
  inline BuiltinHeader const* declare(BuiltinHeader::Value tag) {
    return declare(BuiltinHeader{tag});
  }

  /// Returns a pointer to the unique instance identifying a lambda having the given API.
  ///
  /// The API is a list of type headers. The first denotes the type of the lambda's environment,
  /// the second denotes the return type, and the remainder denotes the types of the parameters.
  StructHeader const* declare_lambda(std::vector<TypeHeader const*>&& api);

  /// Assigns a metatype definition to `type`.
  ///
  /// - Requires: `type` has been declared and never explicitly defined in `this`.
  Metatype const& define(StructHeader const* type, std::vector<Field>&&);

  /// Assigns a metatype definition to `type`.
  ///
  /// - Requires: `type` has been declared and never explicitly defined in `this`.
  Metatype const& define(EnumHeader const* type, std::vector<Field>&&);

  /// Accesses the metatype associated to `type`.
  ///
  /// - Requires: `type` has been declared and defined in `this`.
  Metatype const& operator[](TypeHeader const* type) const;

  /// Returns `true` iff `h` has been declared and defined in `this`.
  inline bool defined(TypeHeader const* h) const {
    auto entry = metatype.find(DereferencingKey<TypeHeader>{h});
    return (entry != metatype.end()) && entry->second.defined();
  }

  /// Returns `true` iff instances of `type` do not involve out-of-line storage.
  ///
  /// - Requires `type` has been declared and defined in `this`.
  inline bool is_trivial(TypeHeader const* type) const {
    return (*this)[type].is_trivial();
  }

  /// Returns `true` iff `f` does not involve out-of-line storage.
  inline bool is_trivial(Field const& f) const {
    return !f.out_of_line() && is_trivial(f.type());
  }

  /// Returns `true` iff none of the given fields involves out-of-line storage.
  inline bool all_trivial(std::span<Field const> const& fields) const {
    return std::all_of(fields.begin(), fields.end(), [&](auto const& f) {
      return is_trivial(f);
    });
  }

  /// Returns the size of an instance of `t`.
  ///
  /// - Requires: `type` has been declared and defined in `this`.
  inline std::size_t size(TypeHeader const* type) const {
    return (*this)[type].size();
  }

  /// Returns the size of `field`.
  ///
  /// - Requires: the type of `field` has been declared and defined in `this`.
  inline std::size_t size(Field const& field) const {
    return field.out_of_line() ? sizeof(void*) : size(field.type());
  }

  /// Returns the alignment of an instance of `type`.
  ///
  /// - Requires: `type` has been declared and defined in `this`.
  inline std::size_t alignment(TypeHeader const* type) const {
    return (*this)[type].alignment();
  }

  /// Returns the alignment of `field`.
  ///
  /// - Requires: the type of `field` has been declared and defined in `this`.
  inline std::size_t alignment(Field const& field) const {
    return field.out_of_line() ? alignof(void*) : alignment(field.type());
  }

  /// Returns the number of bytes from the start of one instance of `type` to the start of the next
  /// when stored in contiguous memory.
  ///
  /// - Requires: `type` has been declared and defined in `this`.
  inline std::size_t stride(TypeHeader const* type) const {
    auto x = round_up_to_nearest_multiple(size(type), alignment(type));
    return x < 1 ? 1 : x;
  }

  /// Returns the offset of the `i`-th field of `m`.
  ///
  /// - Note: An instance of a sum type with more than two cases has only one field, representing
  ///   its tag. The payload is stored at the base address and is not counted as a field. Sum types
  ///   with less than two cases have no tag and thus no field.
  ///
  /// - Requires: `m` is the metatype of a product or sum type that has been declared and defined
  ///   in `this`, and `i` is less the number of fields in `m`.
  inline std::size_t offset(Metatype const& m, std::size_t i) const {
    return m.offsets()[i];
  }

  /// Returns `base` advanced by the offset of the `i`-th field of `m`.
  ///
  /// New storage is allocated iff the field whose address is computed is stored out-of-line and
  /// not already allocated. The returned address points at memory capable of storing an instance
  /// of the field's type.
  ///
  /// - Requires: `m` is the metatype of a product or sum type that has been declared and defined
  ///   in `this`, and `i` is less the number of fields in `m`.
  void* address_of(Metatype const& m, std::size_t i, void* base) const;

  /// Returns `base` advanced by the offset of the `i`-th field of `type`.
  ///
  /// New storage is allocated iff the field whose address is computed is stored out-of-line and
  /// not already allocated. The returned address points at memory capable of storing an instance
  /// of the field's type.
  ///
  /// - Requires: `type` has been declared and defined in `this` and `i` is less the number of
  ///   fields in an instance of `type`.
  inline void* address_of(TypeHeader const* type, std::size_t i, void* base) const {
    return address_of((*this)[type], i, base);
  }

  /// Initializes `target` with a copy of `source`, which is an instance of `type`.
  ///
  /// - Requires: `type` has been declared and defined in `this`.
  template<typename T>
  inline void copy_initialize_builtin(BuiltinHeader const* type, void* target, T source) const {
    if (size(type) != sizeof(T)) { throw std::invalid_argument("bad source"); }
    copy_initialize(type, target, &source);
  }


  /// Initializes `target` with the value of `function`, which is a function pointer.
  template<typename T>
  inline void copy_initialize_function(void* target, T function) {
    auto h = declare(BuiltinHeader::fun);
    copy_initialize_builtin(h, target, reinterpret_cast<AnyFunction>(function));
  }

  /// Initializes `target`, which points to storage for an instance of `type`, to a copy of the
  /// value stored at `source`, which is an instance of the `tag`-th case of `type`.
  ///
  /// - Requires: `type` has been declared and defined in `this`.
  void copy_initialize_enum(
    EnumHeader const* type, std::size_t tag, void* target, void* source
  ) const;

  /// Initializes `target` with a copy of the instance of `type` that is stored at `source`.
  ///
  /// - Requires: `type` has been declared and defined in `this`.
  inline void copy_initialize(TypeHeader const* type, void* target, void* source) const {
    type->copy_initialize(target, source, *this);
  }

  /// Implements `copy_initialize` for built-in types.
  inline void copy_initialize(BuiltinHeader const* h, void* target, void* source) const {
    memcpy(target, source, size(h));
  }

  /// Implements `copy_initialize` for struct types.
  void copy_initialize(StructHeader const* h, void* target, void* source) const;

  /// Implements `copy_initialize` for enum types.
  void copy_initialize(EnumHeader const* h, void* target, void* source) const;

  /// Destroys the instance of `type` that is stored at `source`.
  ///
  /// - Requires: `type` has been declared and defined in `this`.
  inline void deinitialize(TypeHeader const* type, void* source) const {
    type->deinitialize(source, *this);
  }

  /// Implements `deinitialize` for built-in types.
  inline void deinitialize(BuiltinHeader const* h, void* source) const {}

  /// Implements `deinitialize` for struct types.
  void deinitialize(StructHeader const* h, void* source) const;

  /// Implements `deinitialize` for enum types.
  void deinitialize(EnumHeader const* h, void* source) const;

  /// Deinitializes the value of `field`, which is stored at `source`.
  ///
  /// - Requires: the type of `field` has been declared and defined in `this`.
  void deinitialize(Field const& field, void* source) const;

  /// Writes to `stream` a textual representation of the value stored at `source`, which is an
  /// instance of `type`.
  ///
  /// - Requires: `type` has been declared and defined in `this` and `source` is initialzed.
  inline void dump_instance(std::ostream& stream, TypeHeader const* type, void* source) const {
    type->dump_instance(stream, source, *this);
  }

  /// Implements `dump_instance` for built-in types.
  void dump_instance(std::ostream& stream, BuiltinHeader const* type, void* source) const;

  /// Implements `dump_instance` for struct types.
  void dump_instance(std::ostream& stream, StructHeader const* type, void* source) const;

  /// Implements `dump_instance` for enum types.
  void dump_instance(std::ostream& stream, EnumHeader const* type, void* source) const;

  /// Returns a description of the value stored at `source`, which is an instance of `type`.
  inline std::string describe_instance(TypeHeader const* type, void* source) const {
    std::stringstream o;
    dump_instance(o, type, source);
    return o.str();
  }

};

template<>
struct MetatypeConstructor<BuiltinHeader> {

  inline Metatype operator()(BuiltinHeader const* h, TypeStore&) {
    return Metatype{h->size(), h->alignment(), true, {}, {}};
  }

};

}
