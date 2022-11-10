#include <iostream>

namespace templates::adt {

// hopefully without std::variant...
// #include <variant>

// invariant

template <typename T>
struct List {};

template <typename T>
struct Nil : List<T> {};

template <typename T>
struct Cons : List<T> {};

// now variadic..?

// neat!

template <typename... Ts>
struct VList {
  // using types = Ts...;
};

struct VNil : VList<> {};

template <typename T, typename... Ts>
struct VCons : VList<T, Ts...> {
  using head = T;
  using tail = VList<Ts...>;
};

// these aren't necessarily important to the example, but useful in general?
namespace get::at::impl {

template <size_t i, typename T0, typename... Ts>
struct f {
  using type = f<i - 1, Ts...>;
};

template <typename T0, typename... Ts>
struct f<0, T0, Ts...> {
  using type = T0;
};

}  // namespace get::at::impl

template <size_t i, typename... Ts>
using get_at = typename get::at::impl::f<i, Ts...>::type;

}  // namespace templates::adt

int main(int argc, char* argv[]) {
  std::cout << "compiled!" << std::endl;
  return 0;
}
