#pragma once

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef uint8_t XSTBool;
typedef uintptr_t XSTField;

typedef struct XSTTypeMetadata const* XSTTypeMetadataReference;
typedef struct XSTTypeHeader const* XSTTypeHeaderReference;
typedef struct XSTTypeStore* XSTTypeStoreReference;

typedef enum {
  XSTBuiltinTagI1,
  XSTBuiltinTagI32,
  XSTBuiltinTagI64,
  XSTBuiltinTagPointer,
  XSTBuiltinTagFunction,
} XSTBuiltinTag;

/// Creates a new instance of a type store.
XSTTypeStoreReference xst_create_store();

/// Deletes the given type store.
void xst_dispose_store(XSTTypeStoreReference);

/// Returns a pointer to the unique instance identifying the given tag.
XSTTypeHeaderReference xst_declare_builtin(XSTTypeStoreReference, XSTBuiltinTag);

/// Returns `true` iff the given
XSTBool xst_is_defined(XSTTypeStoreReference, XSTTypeHeaderReference);

/// Returns a pointer to the unique instance identifying the application of a struct constructor
/// to the given type arguments.
XSTTypeHeaderReference xst_declare_struct(
  XSTTypeStoreReference, const char*, XSTTypeHeaderReference*, size_t
);

/// Assigns a metatype definition to the given type.
void xst_define_struct(XSTTypeStoreReference, XSTTypeHeaderReference, XSTField*, size_t);

/// Returns the size of the given type.
size_t xst_size(XSTTypeStoreReference, XSTTypeHeaderReference);

/// Returns the alignment of the given type.
size_t xst_alignment(XSTTypeStoreReference, XSTTypeHeaderReference);

/// Creates a field with the given properties.
XSTField xst_create_field(XSTTypeHeaderReference, XSTBool);

#ifdef __cplusplus
}
#endif
