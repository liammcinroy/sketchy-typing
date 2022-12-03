#include <concepts>
#include <iostream>
#include <type_traits>

namespace protos::enums {

enum Vertices { a, b, c };

template <typename E>
concept _Enum = requires {
  requires(std::is_enum_v<E>);
};

template <_Enum E>
struct IsEnum {};

// works, as expected.
using test1 = IsEnum<Vertices>;

// now, we are going to try to allow building `enum`s of `enum`s,
// i.e. representing the 1-simplices explicitly.

// TODO: whether to represent simplicial sets as functors of
// standard simplices to sets, or just as tuples with the given degeneracies?
// I think the latter is easier computationally

namespace simpsets {

namespace details {

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

// Implements `_Pack`
template <typename... _Ts>
struct Pack {
  static constexpr size_t n = sizeof...(_Ts);

  template <size_t i>
  using at = typename std::
      conditional_t<0 <= i && i <= n - 1, get::at<i, _Ts...>, void>;

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

template <typename T>
concept _Pack = requires {
  T::template at<size_t>;

  { T::n } -> std::same_as<const size_t>;  // does work!
};

//// some sort of meaningful `for`
namespace forloop {
template <size_t start,
          size_t end,
          _Pack pack,
          template <typename...>
          class constr,
          bool cont>
struct impl {};

template <size_t start,
          size_t end,
          _Pack pack,
          template <typename...>
          class constr>
struct impl<start, end, pack, constr, false> {
  using type = constr<>;
};

template <size_t start,
          size_t end,
          _Pack pack,
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
          _Pack pack,
          template <typename...> class constr = Pack>
using for_loop =
    typename forloop::impl<start, end, pack, constr, start <= end - 1>::type;

// I'd like to figure out a clean way of doing this for arbitrary inputs,
// i.e. tuples of inputs, but this `brute::pairs` example is supposed to
// just be testing the intuition/basic constructs.
// namespace brute::pairs {
// namespace impl {
// template <template <typename...> class constr,
//           _Pack _Ts1,
//           _Pack _Ts2,
//           size_t counter1,
//           size_t counter2>
// struct pairs {
//   static constexpr size_t _new_counter1 =
//       (counter2 == 0) ? counter1 - 1 : counter1;
//   static constexpr size_t _new_counter1 =
//       (counter2 == 0) ? _Ts2::n : counter2 - 1;
//
//   using type =
//       typename pairs<constr, _Ts1, _Ts2, _new_counter1,
//       _new_counter2>::type::
//           template postapply<constr<typename _Ts1::template at<counter1>,
//                                     typename _Ts2::template at<counter2>>>;
// };
//
// template <template <typename...> class constr, _Pack _Ts1, _Pack _Ts2>
// struct pairs<constr, _Ts1, _Ts2, 0, 0> {
//   using type = constr<>;
// };
//
// }  // namespace impl
//
// template <template <typename...> class constr, _Pack _Ts1, _Pack _Ts2>
// using pairs = typename impl::pairs<constr, _Ts1, _Ts2, _Ts1::n,
// _Ts2::n>::type; }  // namespace brute::pairs
//
// template <_Pack _Ts1, _Pack _Ts2, template <typename...> class constr =
// Pack> using brute_pairs = typename brute::pairs::pairs<constr, _Ts1, _Ts2>;

// TODO

namespace boolevals {
namespace simplicial {

// Condition (i) of `identities<...>()`
namespace condition_i {

template <size_t n, typename TruncSimpSet>
constexpr bool _proper_dimensions() {
  return TruncSimpSet::Set<n>::_dim == n;
}

}  // namespace condition_i

// Condition (ii) of `identities<...>()`
namespace condition_ii {

template <typename simplex, size_t _face_codomain_max, size_t face_idx>
constexpr bool _impl_face_codomains() {
  return (simplex::face<face_idx> < _face_codomain_max)
             ? _impl_face_codomains<simplex,
                                    _face_codomain_max,
                                    face_idx - 1>()
             : false;
}

template <typename simplex, size_t _face_codomain_max>
constexpr bool _impl_face_codomains<simplex, _face_codomain_max, 0>() {
  return simplex::face<0> < _face_codomain_max;
}

template <typename simplex, size_t _face_codomain_max>
constexpr bool _face_codomains() {
  return _impl_face_codomains<simplex, _face_codomain_max, simplex::_dim>();
}

template <size_t n, typename TruncSimpSet, size_t simplex_idx>
constexpr bool _impl_codomains() {
  using set = typename TruncSimpSet::Set<n>;
  using simplex = typename Set::materialize<(typename set::_)simplex_idx>;
  return (_face_codomains<simplex, TruncSimpSet::Set<n - 1>::_n_primitives>())
             ? _impl_codomains<n, TruncSimpSet, simplex_idx - 1>()
             : false;
}

template <size_t n, typename TruncSimpSet>
constexpr bool _impl_codomains<n, TruncSimpSet, 0>() {
  using set = typename TruncSimpSet::Set<n>;
  using simplex = typename Set::materialize<(typename set::_)simplex_idx>;
  return _face_codomains<simplex, TruncSimpSet::Set<n - 1>::_n_primitives>();
}

// TODO: handle edge cases around `n`...?
template <size_t n, typename TruncSimpSet>
constexpr bool _codomains() {
  return _impl_codomains<n,
                         TruncSimpSet,
                         TruncSimpSet::Set<n>::_n_primitives>();
}

}  // namespace condition_ii

// Condition (iii) of `identities<...>()`
namespace condition_iii {
  // TODO: looping, conditions around `n` are complicated...
}  // namespace condition_iii

// the `_TruncatedSimplicialSet` concept says that
// each `typename TruncSimpSet::Set<size_t>` is `_SimplexSetEnum`.
//
// so, the simplicial identities will say that, for each
// `0 <= n < _dim`, then
//   (i)   `using Set = TruncSimpSet::Set<n>;`
//         has `Set::_dim == n`, i.e. the dimensions match.
//   (ii)  For each `0 <= s < Set::_n_primitives`,
//         `using S = Set::materialize<(Set::_)s>` already satisfies
//         `_Simplex<Set::_dim, S>`. So we'll check for each
//         `0 <= i <= S::_dim` that
//         `S::face<i> <= TruncSimpSet::Set<n - 1>::_n_primitives`.
//         i.e. the degeneracy lands in the right place
//         (TODO: for non-primitives, this might get odd.. applies to iii too).
//   (iii) We now know that the `S::face`s are well-defined, hence
//         we need only check the simplicial identities, i.e. for each
//         `0 <= i < j <= S::_dim` that
//         `TruncSimpSet<n - 1>::materialize<S::face<j>>::face<i> ==
//         `TruncSimpSet<n - 1>::materialize<S::face<i>>::face<j - 1>`.
template <size_t _dim, typename TruncSimpSet>
constexpr bool identities() {
  // TODO: link up and fix all the many many errors
  return true;
}

}  // namespace simplicial
}  // namespace boolevals
}  // namespace details

template <size_t _dim, typename s>
concept _Simplex = (
    requires { _dim <= 0; } ||
    requires {
      // the dimension of the simplex.
      requires(s::_dim == _dim);

      // we don't require the degeneracies here, that's handled in the
      // `_SimplicialSet`.
      // but in reality, they will yield `constexpr enum` values of the
      // lower dimensional simplicial sets.
      s::template face<size_t>;
    });

template <typename WE>
concept _SimplexSetEnum = requires {
  // the dimension of the simplicial set
  { WE::_dim } -> std::same_as<const size_t>;

  // use this instead if we add a `size_t _dim` parameter to the
  // `_SimplexSetEnum` template interface.
  // requires(WE::_dim == _dim);

  // the primitives count of the simplicial set.
  // note that the primitives are enumerated in `typename WE::_`, and
  // we assume that these are in order without gaps (i.e.
  // `typename WE::_(0)` is a member, as is `typename WE::_(i)` for
  // `i < _n_primitives`.
  // TODO: maybe check this explicitly using "smart enum techniques".
  { WE::_n_primitives } -> std::same_as<const size_t>;

  // the underlying `enum` (to distinguish members of the set)
  requires(std::is_enum_v<typename WE::_>);

  // a type constructor for each `enum`, i.e. each of the
  // points in the simplicial set, provided the `constexpr enum` value.
  WE::template materialize<typename WE::_>;

  // now, requires that each materialized type is a `_Simplex`,
  // with appropriate matching dimension.
  // we still don't yet require that the simplices in the set satisfy
  // the simplicial identities, that must be handled in the simplicial set
  // once we have access to all of the simplicial sets.
  requires _Simplex<WE::_dim,
                    typename WE::template materialize<typename WE::_>>;
};

template <size_t _dim, typename TS>
concept _TruncatedSimplicialSet = requires {
  // the simplicial set defined at each level, truncated after n.
  // (note that truncation isn't actually checked.)
  { TS::template Sets<size_t> } -> _SimplexSetEnum;

  // the simplicial identities are satisfied.
  requires(details::boolevals::simplicial::identities<_dim, TS>());
};

}  // namespace simpsets

}  // namespace protos::enums

int main(int argc, char* argv[]) {
  std::cout << "compiled!" << std::endl;
  return 0;
}
