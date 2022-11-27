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

  template <size_t i>
  using at2 = void;

  // TODO: maybe make `apply` enhance to `T` with `unapply`?
  // make this whole idea a lil more rigorous.
};

//// as a dumb test of concepts, I just want to check that this does in
//// fact compile. (Spoiler: it doesn't if overspecified?).
namespace implts::test::concepts {
template <typename T>
concept ImplTsConcept = requires {
  // typename T::template at<size_t>;  <-- doesn't work
  T::template at<size_t>;  // does work!

  { T::n } -> std::same_as<const size_t>;  // does work!

  // but so far, we don't express the constraint that ::at is only
  // defined for 0 <= i < n.
  // perhaps we can do this with some ``projective'' types?
};

template <ImplTsConcept T>
struct testConcept {};

using test1 = testConcept<ImplTs<int>>;

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
  using type = typename pairs<constr, _Ts1, _Ts2, counter - 1>::type::
      template postapply<
          constr<typename _Ts1::template at<counter / _Ts1::n>,
                 typename _Ts2::template at<counter % _Ts1::n>>>;
};

template <template <typename...> class constr, typename _Ts1, typename _Ts2>
struct pairs<constr, _Ts1, _Ts2, 0> {
  using type = constr<>;
};

}  // namespace impl

template <template <typename...> class constr, typename _Ts1, typename _Ts2>
using pairs =
    typename impl::pairs<constr, _Ts1, _Ts2, _Ts1::n * _Ts2::n>::type;
}  // namespace brute::pairs

template <typename _Ts1,
          typename _Ts2,
          template <typename...> class constr = ImplTs>
using brute_pairs = typename brute::pairs::pairs<constr, _Ts1, _Ts2>;

//// this is a less dumb test of concepts... one which extends `ImplTsConcept`
namespace implts::test::concepts {

namespace boolevals {

template <typename T>
struct non_void {
  // note that
  // static constexpr bool value = !requires(std::same_as<T, bool>);
  // doesn't work, but the below does!
  static constexpr bool value = !std::is_same_v<T, bool>;
};

template <typename T>
constexpr bool non_void_v() {
  return non_void<T>::value;
}

namespace allsat {

template <typename _Ts, template <typename> class cond, size_t idx>
struct all_sat {
  static constexpr bool value = (cond<typename _Ts::template at<idx>>::value)
                                    ? all_sat<_Ts, cond, idx - 1>::value
                                    : false;
};

template <typename _Ts, template <typename> class cond>
struct all_sat<_Ts, cond, 0> {
  static constexpr bool value =
      (_Ts::n > 0) ? cond<typename _Ts::template at<0>>::value : true;
};

}  // namespace allsat

template <typename _Ts, template <typename> class cond>
constexpr bool all_sat_v() {
  return allsat::all_sat<_Ts, cond, _Ts::n - 1>::value;
}

template <typename _Ts>
constexpr bool all_non_void() {
  return all_sat_v<_Ts, non_void>();
}

}  // namespace boolevals

template <typename T>
concept ImplTsConceptExt = requires {
  requires ImplTsConcept<T>;  // has ::template at<size_t> and ::n -> size_t.

  // but so far, we don't express the constraint that ::at is only
  // defined for 0 <= i < n.
  // Let's say we impose that ``defined'' means ``not void'', then (?):
  requires(boolevals::all_non_void<T>());
};

template <typename T>
concept HasValue = requires {
  { T::value } -> std::same_as<const bool>;
};

template <HasValue T>
struct testHasValueNonVoid {};

using test2 = testHasValueNonVoid<boolevals::non_void<int>>;

template <typename T>
concept HasValueAndTrue = requires {
  requires HasValue<T>;
  requires(T::value);
};

template <HasValueAndTrue T>
struct testHasValueAndTrueNonVoid {};

using test3 = testHasValueAndTrueNonVoid<boolevals::non_void<int>>;

template <ImplTsConceptExt T>
struct testConceptExt {};

using test4 = testConceptExt<ImplTs<int>>;

// this shouldn't work
using test5 = testConceptExt<ImplTs<void>>;

}  // namespace implts::test::concepts

}  // namespace templates::projection

int main(int argc, char* argv[]) {
  std::cout << "compiled!" << std::endl;
  return 0;
}
