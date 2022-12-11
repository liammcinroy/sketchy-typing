#include <algorithm>
#include <compare>
#include <concepts>
#include <iostream>
#include <type_traits>

namespace protos::limits {

// now, we are going to try to allow building `enum`s of `enum`s,
// i.e. representing the 1-simplices explicitly.

// TODO: whether to represent simplicial sets as functors of
// standard simplices to sets, or just as tuples with the given degeneracies?
// I think the latter is easier computationally -- but maybe harder to extend
// with other functorial expressions (if we ever get to that point?)

namespace simpsets {

template <size_t _dim, typename s>
concept _Simplex = (
    requires { _dim <= 0; } ||
    requires {
      // the dimension of the simplex.
      requires(s::_dim == _dim);

      // we don't require the degeneracies here, that's handled in the
      // `_SimplicialSet`.
      // but in reality, they will yield classes with
      // `static constexpr size_t ::value` fields to indicate the value
      // of the face.
      s::template face<size_t>;
    });

namespace details::boolevals::simplicial {

template <size_t _dim,
          size_t _n_primitives,
          typename simplexset,
          size_t simplex_idx>
requires _Simplex<_dim,
                  typename simplexset::template materialize<(
                      typename simplexset::_)simplex_idx>>
struct is_primitive_simplex_impl {
  static constexpr bool value =
      is_primitive_simplex_impl<_dim,
                                _n_primitives,
                                simplexset,
                                simplex_idx + 1>::value;
};

template <size_t _dim, size_t _n_primitives, typename simplexset>
requires _Simplex<_dim,
                  typename simplexset::template materialize<(
                      typename simplexset::_)_n_primitives>>
struct is_primitive_simplex_impl<_dim,
                                 _n_primitives,
                                 simplexset,
                                 _n_primitives> {
  static constexpr bool value = true;
};

template <typename simplexset>
struct is_simplex_set {
  static constexpr bool value =
      is_primitive_simplex_impl<simplexset::_dim,
                                simplexset::_n_primitives,
                                simplexset,
                                0>::value;
};

}  // namespace details::boolevals::simplicial

template <typename WE>
concept _SimplexSet = requires {
  // the dimension of the simplicial set
  { WE::_dim } -> std::same_as<const size_t>;

  // use this instead if we add a `size_t _dim` parameter to the
  // `_SimplexSet` template interface.
  // requires(WE::_dim == _dim);

  // the primitives count of the simplicial set.
  // note that the primitives are enumerated in `typename WE::_`, and
  // we assume that these are in order without gaps (i.e.
  // `typename WE::_(0)` is a member, as is `typename WE::_(i)` for
  // `i < _n_primitives`.
  // TODO: maybe check this explicitly using "smart enum techniques".
  { WE::_n_primitives } -> std::same_as<const size_t>;

  // the underlying "enum" (to distinguish members of the set)
  requires(std::is_convertible_v<typename WE::_, const size_t>);

  // a type constructor for each "enum", i.e. each of the
  // points in the simplicial set, provided the `constexpr enum` value.

  // now, requires that each materialized type is a `_Simplex`,
  // with appropriate matching dimension.
  // we still don't yet require that the simplices in the set satisfy
  // the simplicial identities, that must be handled in the simplicial set
  // once we have access to all of the simplicial sets.
  requires(details::boolevals::simplicial::is_simplex_set<WE>::value);
};

namespace details::boolevals::simplicial {

template <size_t _dim, typename simpset, size_t n>
requires _SimplexSet<typename simpset::template Set<n>>
struct is_simplex_set_impl {
  static constexpr bool value =
      is_simplex_set_impl<_dim, simpset, n + 1>::value;
};

template <size_t _dim, typename simpset>
requires _SimplexSet<typename simpset::template Set<_dim>>
struct is_simplex_set_impl<_dim, simpset, _dim> {
  static constexpr bool value = true;
};

template <size_t _dim, typename simpset>
struct is_simplicial_set {
  static constexpr bool value = is_simplex_set_impl<_dim, simpset, 0>::value;
};

}  // namespace details::boolevals::simplicial

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

namespace boolevals {
namespace simplicial {

// Condition (i) of `identities<...>()`
namespace condition_i {

template <size_t n, typename simpset>
struct _proper_dimensions {
  static constexpr bool value = simpset::template Set<n>::_dim == n;
};

}  // namespace condition_i

// Condition (ii) of `identities<...>()`
namespace condition_ii {

template <size_t targ_n, typename simplex, size_t face_idx>
requires _Simplex<targ_n, typename simplex::template face<face_idx>>
struct _impl_face_codomains {
  static constexpr bool value =
      _impl_face_codomains<targ_n, simplex, face_idx - 1>::value;
};

template <size_t targ_n, typename simplex>
requires _Simplex<targ_n, typename simplex::template face<0>>
struct _impl_face_codomains<targ_n, simplex, 0> {
  static constexpr bool value = true;
};

template <size_t targ_n, typename simplex>
constexpr bool _face_codomains() {
  return _impl_face_codomains<targ_n, simplex, simplex::_dim>::value;
}

template <size_t n, typename simpset, size_t simplex_idx>
struct _impl_codomains {
  using set = typename simpset::template Set<n>;
  using simplex =
      typename set::template materialize<(typename set::_)simplex_idx>::type;
  static constexpr bool value =
      (_face_codomains<n - 1, simplex>())
          ? _impl_codomains<n, simpset, simplex_idx - 1>::value
          : false;
};

template <size_t n, typename simpset>
struct _impl_codomains<n, simpset, 0> {
  using set = typename simpset::template Set<n>;
  using simplex = typename set::template materialize<(typename set::_)0>::type;
  static constexpr bool value = _face_codomains<n - 1, simplex>();
};

template <size_t n, typename simpset>
struct _codomains {
  static constexpr bool value =
      _impl_codomains<n, simpset, simpset::template Set<n>::_n_primitives>::
          value;
};

template <typename simpset>
struct _codomains<0, simpset> {
  static constexpr bool value = true;
};

}  // namespace condition_ii

// Condition (iii) of `identities<...>()`
namespace condition_iii {

template <size_t n, typename simplex, size_t i, size_t j>
requires std::same_as<
    typename simplex::template face<j>::type::template face<i>::type,
    typename simplex::template face<i>::type::template face<
        j - 1>::type> struct _impl_simplex_degeneracies {
  static constexpr size_t newi = (i > 0) ? i - 1 : j - 2;
  static constexpr size_t newj = (i > 0) ? j : j - 1;
  static constexpr bool value =
      _impl_simplex_degeneracies<n, simplex, newi, newj>::value;
};

template <size_t n, typename simplex>
requires std::same_as<
    typename simplex::template face<1>::type::template face<0>::type,
    typename simplex::template face<0>::type::template face<
        0>::type> struct _impl_simplex_degeneracies<n, simplex, 0, 1> {
  static constexpr bool value = true;
};

template <size_t n, typename simplex>
constexpr bool _simplex_degeneracies() {
  return _impl_simplex_degeneracies<n, simplex, n - 1, n>::value;
}

template <size_t n, typename simpset, size_t simplex_idx>
struct _impl_degeneracies {
  using set = typename simpset::template Set<n>;
  using simplex =
      typename set::template materialize<(typename set::_)simplex_idx>::type;
  static constexpr bool value =
      (_simplex_degeneracies<n, simplex>())
          ? _impl_degeneracies<n, simpset, simplex_idx - 1>::value
          : false;
};

template <size_t n, typename simpset>
struct _impl_degeneracies<n, simpset, 0> {
  using set = typename simpset::template Set<n>;
  using simplex = typename set::template materialize<(typename set::_)0>::type;
  static constexpr bool value = _simplex_degeneracies<n, simplex>();
};

template <size_t n, typename simpset>
struct _degeneracies {
  static constexpr bool value =
      _impl_degeneracies<n, simpset, simpset::template Set<n>::_n_primitives>::
          value;
};

template <typename simpset>
struct _degeneracies<1, simpset> {
  static constexpr bool value = true;
};

template <typename simpset>
struct _degeneracies<0, simpset> {
  static constexpr bool value = true;
};

}  // namespace condition_iii

// Passing for 0-simplex
// Identities, dims passing for 1-simplex, codomains failing

template <size_t _dim, typename simpset, size_t n>
requires(condition_i::_proper_dimensions<n, simpset>::value&&
             condition_ii::_codomains<n, simpset>::value&& condition_iii::
                 _degeneracies<n, simpset>::value) struct _impl_identities {
  static constexpr bool value = _impl_identities<_dim, simpset, n + 1>::value;
};

template <size_t _dim, typename simpset>
requires(condition_i::_proper_dimensions<_dim, simpset>::value&&
             condition_ii::_codomains<_dim, simpset>::value&&
                 condition_iii::_degeneracies<_dim, simpset>::
                     value) struct _impl_identities<_dim, simpset, _dim> {
  static constexpr bool value = true;
};

// the `_TruncatedSimplicialSet` concept says that
// each `typename TruncSimpSet::Set<size_t>` is `_SimplexSet`.
//
// so, the simplicial identities will say that, for each
// `0 <= n < _dim`, then
//   (i)   `using Set = TruncSimpSet::Set<n>;`
//         has `Set::_dim == n`, i.e. the dimensions match.
//   (ii)  For each `0 <= s < Set::_n_primitives`,
//         `using S = Set::materialize<(Set::_)s>` already satisfies
//         `_Simplex<Set::_dim, S>`. So we'll check for each
//         `0 <= i <= S::_dim` that
//         `S::face<i>` is a `_Simplex<n - 1>`.
//         i.e. the degeneracy lands in the right place.
//         TODO: check well-defined wrt simplicial set...
//   (iii) We now know that the `S::face`s are well-defined, hence
//         we need only check the simplicial identities, i.e. for each
//         `0 <= i < j <= S::_dim` that
//         `S::face<j>::face<i> == S::face<i>::face<j - 1>`.
template <size_t _dim, typename simpset>
struct identities {
  static constexpr bool value = _impl_identities<_dim, simpset, 0>::value;
};

}  // namespace simplicial
}  // namespace boolevals
}  // namespace details

template <size_t _dim, typename TS>
concept _TruncatedSimplicialSet = requires {
  // the simplicial set defined at each level, truncated after n.
  // (note that truncation isn't actually checked.)
  // Basically checking:
  // { typename TS::template Set<size_t> } -> _SimplexSet;
  requires(details::boolevals::simplicial::is_simplicial_set<_dim, TS>::value);

  // the simplicial identities are satisfied.
  requires(details::boolevals::simplicial::identities<_dim, TS>::value);
};

}  // namespace simpsets

namespace simpsets::tests {

// this is a gross way of writing the standard 2-simplex
struct Standard2Simplex {
  template <size_t n>
  struct Set;

  template <>
  struct Set<0> {
    static constexpr size_t _dim = 0;

    static constexpr size_t _n_primitives = 2;

    enum _ { A, B, C };

    // TODO: these aren't very illuminating underlying types...
    // it only works in this case since they are 0-simplices

    template <_ object>
    struct materialize;

    template <>
    struct materialize<_::A> {
      using type = void;
    };

    template <>
    struct materialize<_::B> {
      using type = void;
    };

    template <>
    struct materialize<_::C> {
      using type = void;
    };
  };

  template <>
  struct Set<1> {
    static constexpr size_t _dim = 1;

    static constexpr size_t _n_primitives = 2;

    enum _ { f, g, gf };

    // TODO: helper to create simplices of prior ones...

    struct _f_type {
      static constexpr size_t _dim = 1;

      template <size_t i>
      struct face;

      template <>
      struct face<0> {
        using type = typename Set<0>::template materialize<Set<0>::_::A>::type;
      };

      template <>
      struct face<1> {
        using type = typename Set<0>::template materialize<Set<0>::_::B>::type;
      };
    };

    struct _g_type {
      static constexpr size_t _dim = 1;

      template <size_t i>
      struct face;

      template <>
      struct face<0> {
        using type = typename Set<0>::template materialize<Set<0>::_::B>::type;
      };

      template <>
      struct face<1> {
        using type = typename Set<0>::template materialize<Set<0>::_::C>::type;
      };
    };

    struct _gf_type {
      static constexpr size_t _dim = 1;

      template <size_t i>
      struct face;

      template <>
      struct face<0> {
        using type = typename Set<0>::template materialize<Set<0>::_::A>::type;
      };

      template <>
      struct face<1> {
        using type = typename Set<0>::template materialize<Set<0>::_::C>::type;
      };
    };

    template <_ object>
    struct materialize;

    template <>
    struct materialize<_::f> {
      using type = _f_type;
    };

    template <>
    struct materialize<_::g> {
      using type = _g_type;
    };

    template <>
    struct materialize<_::gf> {
      using type = _gf_type;
    };
  };

  template <>
  struct Set<2> {
    static constexpr size_t _dim = 2;

    static constexpr size_t _n_primitives = 0;

    enum _ { gfcomp };

    // TODO: helper to create simplices of prior ones...

    struct _gf_comp_type {
      static constexpr size_t _dim = 2;

      template <size_t i>
      struct face;

      template <>
      struct face<0> {
        using type = typename Set<1>::template materialize<Set<1>::_::f>::type;
      };

      template <>
      struct face<1> {
        using type =
            typename Set<1>::template materialize<Set<1>::_::gf>::type;
      };

      template <>
      struct face<2> {
        using type = typename Set<1>::template materialize<Set<1>::_::g>::type;
      };
    };

    template <_ object>
    struct materialize {
      using type = _gf_comp_type;
    };
  };
};

template <size_t _dim, typename simpset>
requires _TruncatedSimplicialSet<_dim, simpset>
struct RequiresTruncated {
};

using testStandard2Simplex0Truncated = RequiresTruncated<0, Standard2Simplex>;
using testStandard2Simplex1Truncated = RequiresTruncated<1, Standard2Simplex>;
using testStandard2Simplex2Truncated = RequiresTruncated<2, Standard2Simplex>;

template <size_t n>
struct StandardSimplex {
  // creates a unique new type for each wrapping `uid`.
  // but it really should just be the "same" as `V`, without
  // satisfying `std::same_as<V>`.
  template <size_t _uid, typename V>
  struct FormedVertex {
    using original = V;
    static constexpr size_t uid = _uid;

    V _value;
    constexpr FormedVertex(const V& val) { _value = val; }
    auto operator<=>(const FormedVertex&) const = default;
    operator V() const { return _value; }

    template <size_t new_uid>
    using replace_uid = FormedVertex<new_uid, V>;
  };

  // The idea being, we only ``define'' one `StandardSimplex<n - 1>`
  // but wrap it several times to obtain the other `n + 1` necessary
  // copies.
  //
  // There is one trick,
  template <size_t __dim,
            typename S,
            template <size_t, size_t, typename>
            class W>
  requires _Simplex<__dim, S>
  struct FormedSimplex {
    struct type {
      static constexpr size_t _dim = __dim;

      // each `face<i>` is supposed to have a `::type`, so this is ok,
      // and we want each `face<i>` to have a `::type` so we can do the
      // base case of `FormedVertex`.
      template <size_t i>
      using face = FormedSimplex<
          _dim - 1,
          typename W<_dim, i, typename S::template face<i>::type>::type,
          W>;
    };
  };

  template <typename S, template <size_t, size_t, typename> class W>
  requires _Simplex<0, typename S::original> &&
      std::is_convertible_v<S::uid, const size_t>
  struct FormedSimplex<0, S, W> {
    using type = FormedVertex<S::uid, typename S::original>;
  };

  template <size_t nn>
  struct _Set {
    static constexpr size_t _dim = nn;
  };

  template <size_t i>
  using Set = std::conditional_t<0 <= i && i <= n, _Set<i>, void>;
};

// crazily, we have to put this outside of the definition of
// `StandardSimplex` to prevent "instantiated within its own definition"
// errors.
template <size_t n>
struct StandardSimplex<n>::_Set<0> {
  static constexpr size_t _dim = 0;
  static constexpr size_t _n_primitives = n;

  using _ = size_t;

  template <_ object>
  struct materialize {
    using type = FormedVertex<object,
                              typename StandardSimplex<0>::template Set<
                                  0>::template materialize<0>::type>;
  };
};

template <>
struct StandardSimplex<0> {
  template <size_t i>
  struct Set {};

  template <>
  struct Set<0> {
    static constexpr size_t _dim = 0;
    static constexpr size_t _n_primitives = 0;

    using _ = size_t;

    template <_ object>
    struct materialize;

    template <>
    struct materialize<0> {
      using type = void;
    };
  };
};

using testStandard0Simplex0Truncated =
    RequiresTruncated<0, StandardSimplex<0>>;

}  // namespace simpsets::tests

}  // namespace protos::limits

int main(int argc, char* argv[]) {
  using simpset = protos::limits::simpsets::tests::Standard2Simplex;
  using simplexset0 = typename simpset::template Set<0>;
  auto asString0 = [](const simplexset0::_ s) {
    if (s == simplexset0::_::A) return "A";
    if (s == simplexset0::_::B)
      return "B";
    else
      return "C";
  };
  using simplexset1 = typename simpset::template Set<1>;
  auto asString1 = [](const simplexset1::_ s) {
    if (s == simplexset1::_::f) return "f : A -> B";
    if (s == simplexset1::_::g)
      return "g : B -> C";
    else
      return "gf : A -> C";
  };

  using simplex2 = typename simpset::template Set<2>::materialize<(
      typename simpset::template Set<2>::_)0>::type;

  // std::cout << "2 simplex degeneraceis:" << std::endl;
  {
#define print_degeneracies(I, J, it)                                          \
  constexpr size_t i##it = I;                                                 \
  constexpr size_t j##it = J;                                                 \
  std::cout                                                                   \
      << "\ti = " << i##it << ", j = " << j##it << ": "                       \
      << asString0(simplexset1::template materialize<simplex2::template face< \
                       j##it>::value>::type::template face<i##it>::value)     \
      << ";\tj = " << j##it - 1 << ", i = " << i##it << ": "                  \
      << asString0(simplexset1::template materialize<simplex2::template face< \
                       i##it>::value>::type::template face<j##it - 1>::value) \
      << std::endl;

    // print_degeneracies(1, 2, 0) print_degeneracies(0, 2, 1)
    //     print_degeneracies(0, 1, 2)
#undef print_degeneracies
  }

  std::cout << "compiled!" << std::endl;
  return 0;
}
