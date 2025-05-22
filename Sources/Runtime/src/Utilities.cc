#include "Utilities.h"

namespace xst {

void precondition(bool test, std::string const& error) {
  if (!test) { throw std::logic_error(error); }
}

void* aligned_alloc(std::size_t a, std::size_t s, bool zero_initialize) {
  if (s == 0) { return nullptr; }

  using Head = std::size_t;

  auto x = std::max(a, alignof(Head)) - 1;
  auto b = new std::byte[sizeof(Head) + s + x];

  Head offset = round_up_to_nearest_multiple(sizeof(Head), a);
  auto payload = b + offset;
  auto head = payload - sizeof(Head);
  memcpy(head, &offset, sizeof(Head));

  if (zero_initialize) {
    std::memset(payload, 0, s);
  }

  return payload;
}

void aligned_free(void* p) {
  if (p == nullptr) { return; }

  using Head = std::size_t;

  Head offset;
  auto payload = static_cast<std::byte*>(p);
  auto head = payload - sizeof(Head);
  memcpy(&offset, head, sizeof(Head));
  auto b = payload - offset;
  delete[] b;
}

}
