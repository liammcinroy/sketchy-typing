#include <concepts>
#include <iostream>
#include <type_traits>

namespace templates::projection {

//// Basic usual index variadic
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

// basic idea is that we to create new variadic parameter packs
// out of pre-existing ones.
//
// E.g. pairs<cont<T1, T2, ...>, cont<S1, S2, ...>>::type is
// cont<(T1, S1), (T1, S2), ..., (T2, S1), ...>

// template <size_t _n, typename... _Ts>
// concept SArray = requires {
//   requires(_n == sizeof...(_Ts));
// };

template <typename... _Ts>
struct ImplTs {
  static constexpr size_t n = sizeof...(_Ts);

  template <size_t i>
  using at = typename std::
      conditional<0 <= i && i <= sizeof...(_Ts), get::at<i, _Ts...>, void>;

  template <template <typename...> class T, typename... _Ts2>
  struct postapply {
    using type = T<_Ts2..., _Ts...>;
  };

  template <template <typename...> class T, typename... _Ts2>
  struct preapply {
    using type = T<_Ts..., _Ts2...>;
  };

  // TODO: maybe make `apply` enhance to `T` with `unapply`?
  // make this whole idea a lil more rigorous.
};

//// as a dumb test of concepts, I just want to check that this does in
//// fact compile. (Spoiler: it doesn't).
namespace implts::test::concepts {
template <typename T>
concept ImplTsConcept = requires {
  typename T::template at<size_t>;
};

template <ImplTsConcept T>
struct testConcept {};

// ok -- weirdly enough this doesn't work... come back to it later I guess
// using test1 = testConcept<ImplTs<int>>;
}  // namespace implts::test::concepts

//// anyways, back to projection (TODO: would be nice to enforce concept, but
//// meh).

//// some sort of meaningful `for`
namespace forloop {
template <size_t start,
          size_t end,
          typename pack,
          template <typename...>
          class constr,
          bool cont>
struct impl {};

template <size_t start,
          size_t end,
          typename pack,
          template <typename...>
          class constr>
struct impl<start, end, pack, constr, false> {
  using type = constr<>;
};

template <size_t start,
          size_t end,
          typename pack,
          template <typename...>
          class constr>
struct impl<start, end, pack, constr, true> {
  using type =
      typename impl<start + 1, end, pack, constr, start + 1 <= end - 1>::type::
          template postapply<pack::template at<start>>;
};
}  // namespace forloop
template <size_t start,
          size_t end,
          typename pack,
          template <typename...> class constr = ImplTs>
using for_loop =
    typename forloop::impl<start, end, pack, constr, start <= end - 1>::type;

// I'd like to figure out a clean way of doing this for arbitrary inputs,
// i.e. tuples of inputs, but this `brute::pairs` example is supposed to
// just be testing the intuition/basic constructs.
namespace brute::pairs {
namespace impl {
template <template <typename...> class constr,
          typename _Ts1,
          typename _Ts2,
          size_t counter>
struct pairs {
  using type =
      typename pairs<constr, _Ts1, _Ts2, counter - 1>::type::template postapply<
          constr<typename _Ts1::template at<counter / _Ts1::n>,
                 typename _Ts2::template at<counter % _Ts1::n>>>;
};

template <template <typename...> class constr, typename _Ts1, typename _Ts2>
struct pairs<constr, _Ts1, _Ts2, 0> {
  using type = constr<>;
};

}  // namespace impl

template <template <typename...> class constr, typename _Ts1, typename _Ts2>
using pairs = typename impl::pairs<constr, _Ts1, _Ts2, _Ts1::n * _Ts2::n>::type;
}  // namespace brute::pairs

}  // namespace templates::projection

int main(int argc, char* argv[]) {
  std::cout << "compiled!" << std::endl;
  return 0;
}
