#include <concepts>
#include <iostream>
#include <type_traits>

namespace protos::simpsets {

namespace kleene {

namespace get {
template <size_t i, typename T0, typename... Ts>
struct f {
  using type = f<i - 1, Ts...>;
};

template <typename T0, typename... Ts>
struct f<0, T0, Ts...> {
  using type = T0;
};

template <size_t i, typename... Ts>
using at = typename f<i, Ts...>::type;
}  // namespace get

template <typename T>
concept _Pack = requires {
  { T::n } -> std::same_as<const size_t>;

  // we omit the typename at the start of the following lines,
  // because that fails in compilation for some reason.

  T::template at<size_t>;

  // TODO: can we reference `_Pack` within its own definition?
  // I think not...

  T::template postpend<typename...>;
  { T::template postpend<typename...>::type } -> _Pack;

  T::template prepend<typename...>;
  { T::template prepend<typename...>::type } -> _Pack;

  // TODO: concat?
};

// Implements _Pack
template <typename... Ts>
struct Pack {
  static constexpr size_t n = sizeof...(_Ts);

  template <size_t i>
  using at = typename std::conditional_t<0 <= i && i <= n - 1,
                                         get::at<i, Ts...>,
                                         void>;

  template <typename... Ts2>
  struct postpend {
    using type = Pack<Ts2..., Ts...>;
  };

  template <typename... Ts2>
  struct prepend {
    using type = Pack<Ts..., Ts2...>;
  };
};

// TODO: iterators

}  // namespace kleen

namespace simplices {

template <typename S>
concept _Simplex = requires {

  { S::n } -> std::same_as<const size_t>;

  // Would be nice to put a condition on these as simplices themselves,
  // but that might require wrapping each primitive we want in a
  // class to conform to `_Simplex` itself... though that might not be an
  // issue with the disjunction and enough `requires` clauses (similar to
  // `std::is_same_v`).
  S::template face<size_t>;

  // these will use a ''projective'' type as a conjunction over the
  // (suitable) pairs of faces, and those faces' `::template eq<typename>`
  // members...
  // For clarity, or perhaps out of necessity, we may need to eventually
  // split this into separate concepts (e.g. for a `_Vertex` as a base case,
  // or as `_SimplexEq`, or whatever).
  // Maybe if we have a `_Vertex`, which `requires is_enum<...>`, then
  // we get equality already!
  S::template eq<typename>;
  { S::template eq<typename>::value } -> std::same_as<const bool>;
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
      typename std::enable_if_t<0 <= i && i <= n, kleen::get::at<i, Faces...>>;
};

}  // namespace simplices

}  // namespace protos::simpsets

int main(int argc, char* argv[]) {
  std::cout << "compiled!" << std::endl;
  return 0;
}
