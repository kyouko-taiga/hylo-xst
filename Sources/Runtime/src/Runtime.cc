#include "TypeStore.h"
#include "Runtime.h"

namespace xst {

BuiltinHeader::Value tag(XSTBuiltinTag t) {
  switch (t) {
    case XSTBuiltinTagI1:
      return BuiltinHeader::i1;
    case XSTBuiltinTagI32:
      return BuiltinHeader::i32;
    case XSTBuiltinTagI64:
      return BuiltinHeader::i64;
    case XSTBuiltinTagPointer:
      return BuiltinHeader::ptr;
    case XSTBuiltinTagFunction:
      return BuiltinHeader::fun;
  }
}

}

extern "C" {

XSTTypeStoreReference xst_create_store() {
  auto* s = new xst::TypeStore{};
  return reinterpret_cast<XSTTypeStoreReference>(s);
}

void xst_dispose_store(XSTTypeStoreReference s) {
  auto* self = reinterpret_cast<xst::TypeStore*>(s);
  delete self;
}

XSTTypeHeaderReference xst_declare_builtin(XSTTypeStoreReference s, XSTBuiltinTag t) {
  auto* self = reinterpret_cast<xst::TypeStore*>(s);
  auto* result = static_cast<xst::TypeHeader const*>(self->declare(xst::tag(t)));
  return reinterpret_cast<XSTTypeHeaderReference>(result);
}

uint8_t xst_is_defined(XSTTypeStoreReference s, XSTTypeHeaderReference h) {
  auto* self = reinterpret_cast<xst::TypeStore*>(s);
  return self->defined(reinterpret_cast<xst::TypeHeader const*>(h));
}

XSTTypeHeaderReference xst_declare_struct(
  XSTTypeStoreReference s, const char* n, XSTTypeHeaderReference* h, size_t i
) {
  auto* self = reinterpret_cast<xst::TypeStore*>(s);
  auto* result = static_cast<xst::TypeHeader const*>(
    self->declare(xst::StructHeader{std::string{n}, {}}));
  return reinterpret_cast<XSTTypeHeaderReference>(result);
}

void xst_define_struct(XSTTypeStoreReference s, XSTTypeHeaderReference h, XSTField* f, size_t i) {
  auto* self = reinterpret_cast<xst::TypeStore*>(s);
  auto* x0 = reinterpret_cast<xst::TypeHeader const*>(h);
  auto* x1 = dynamic_cast<xst::StructHeader const*>(x0);

  std::vector<xst::Field> fs;
  for (auto j = 0; j < i; ++j) {
    fs.push_back(xst::Field(f[j]));
  }
  self->define(x1, std::move(fs));
}

size_t xst_size(XSTTypeStoreReference s, XSTTypeHeaderReference h) {
  auto* self = reinterpret_cast<xst::TypeStore*>(s);
  return self->size(reinterpret_cast<xst::TypeHeader const*>(h));
}

size_t xst_alignment(XSTTypeStoreReference s, XSTTypeHeaderReference h) {
  auto* self = reinterpret_cast<xst::TypeStore*>(s);
  return self->alignment(reinterpret_cast<xst::TypeHeader const*>(h));
}

XSTField xst_create_field(XSTTypeHeaderReference h, XSTBool out_of_line) {
  auto* type = reinterpret_cast<xst::TypeHeader const*>(h);
  xst::Field f{type, (out_of_line != 0)};
  return f.raw_value;
}

}
