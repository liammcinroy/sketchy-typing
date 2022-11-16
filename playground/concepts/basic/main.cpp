#include <concepts>
#include <iostream>

namespace concepts::basic {

//// Basic testing

template <typename T>
concept HasType = requires {
  typename T::type;
};

// note: implements HasType
template <typename T>
struct ImplHasType {
  using type = T;
};

template <typename T>
concept HasNested = requires {
  typename T::type;
  requires HasType<typename T::type>;

  // { typename T::type } -> HasType; <-- doesn't work
};

// note: implements HasNested
template <HasType T>
struct ImplNested {
  using type = T;
};

template <typename T>
using nest = ImplNested<ImplHasType<T>>;

template <typename T>
using nest_bad = ImplNested<T>;

template <HasNested T>
struct test_nested {};

template <typename T>
using nested = test_nested<nest<T>>;

template <typename T>
using nested_bad = test_nested<T>;

//// template concepts?

// doesn't work:
// template <concept C, typename T>
// concept Nest = requires {
//   typename T::type;
//   requires C<typename T::type>;
// }

// does work (hacky)
// #define 

}  // namespace concepts::basic

int main(int argc, char* argv[]) {
  concepts::basic::nest<int> Test1;
  // concepts::basic::nest_bad<int>;
  concepts::basic::nested<int> Test2;
  // concepts::basic::nest_bad<int>;

  std::cout << "compiled!" << std::endl;
  return 0;
}
