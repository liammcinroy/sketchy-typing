#include <concepts>
#include <iostream>
#include <type_traits>

namespace protos::simpsets {

namespace get {
template <size_t i, typename T0, typename... Ts>
struct f {
  using type = f<i - 1, Ts...>;
};

template <typename T0, typename... Ts>
struct f<0, T0, Ts...> {
  using type = T0;
};

template<size_t i, typename... Ts>
using at = typename f<i, Ts...>::type;
}  // namespace at

namespace simplices {

template <size_t n, typename S>
concept Simplex = requires {
  typename S::template face<size_t>;
  // requires(n > 0 && Simplex<typename S::template face<size_t>>;
};

template <size_t n, typename... Faces>
requires(sizeof...(Faces) == n + 1) // &&
        //  (n == 0 ||
        //   (// something like all<Faces..., Simplex<n - 1>>
        //   )
        //  ))
struct SimplexTrait {
  template <size_t i>
  using face =
      typename std::enable_if_t<0 <= i && i <= n, get::at<i, Faces...>>;
};

}  // namespace simplices

}  // namespace protos::simpsets

int main(int argc, char* argv[]) {
  std::cout << "compiled!" << std::endl;
  return 0;
}
