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
// I think the latter is easier computationally -- but maybe harder to extend
// with other functorial expressions (if we ever get to that point?)

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

template <typename simplex, size_t _face_codomain_max, size_t face_idx>
struct _impl_face_codomains {
  static constexpr bool value =
      (simplex::template face<face_idx>::value <= _face_codomain_max - 1)
          ? _impl_face_codomains<simplex, _face_codomain_max, face_idx - 1>::
                value
          : false;
};

template <typename simplex, size_t _face_codomain_max>
struct _impl_face_codomains<simplex, _face_codomain_max, 0> {
  static constexpr bool value =
      simplex::template face<0>::value <= _face_codomain_max - 1;
};

template <typename simplex, size_t _face_codomain_max>
constexpr bool _face_codomains() {
  return _impl_face_codomains<simplex, _face_codomain_max, simplex::_dim>::
      value;
}

template <size_t n, typename simpset, size_t simplex_idx>
struct _impl_codomains {
  using set = typename simpset::template Set<n>;
  using simplex =
      typename set::template materialize<(typename set::_)simplex_idx>::type;
  static constexpr bool value =
      (_face_codomains<simplex, simpset::template Set<n - 1>::_n_primitives>())
          ? _impl_codomains<n, simpset, simplex_idx - 1>::value
          : false;
};

template <size_t n, typename simpset>
struct _impl_codomains<n, simpset, 0> {
  using set = typename simpset::template Set<n>;
  using simplex = typename set::template materialize<(typename set::_)0>::type;
  static constexpr bool value =
      _face_codomains<simplex, simpset::template Set<n - 1>::_n_primitives>();
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

template <size_t n, typename simplex, typename simpset, size_t i, size_t j>
struct _impl_simplex_degeneracies {
  using lowerset = typename simpset::template Set<n - 1>;
  static constexpr size_t newi = (i > 0) ? i - 1 : j - 2;
  static constexpr size_t newj = (i > 0) ? j : j - 1;
  static constexpr bool value =
      (lowerset::template materialize<(
           typename lowerset::_)j>::type::template face<i>::value ==
       lowerset::template materialize<(
           typename lowerset::_)i>::type::template face<j - 1>::value)
          ? _impl_simplex_degeneracies<n, simplex, simpset, newi, newj>::value
          : false;
};

template <size_t n, typename simplex, typename simpset>
struct _impl_simplex_degeneracies<n, simplex, simpset, 0, 1> {
  using lowerset = typename simpset::template Set<n - 1>;
  static constexpr bool value =
      lowerset::template materialize<(
          typename lowerset::_)1>::type::template face<0>::value ==
      lowerset::template materialize<(
          typename lowerset::_)0>::type::template face<0>::value;
};

template <size_t n, typename simplex, typename simpset>
constexpr bool _simplex_degeneracies() {
  return _impl_simplex_degeneracies<n, simplex, simpset, n - 1, n>::value;
}

template <size_t n, typename simpset, size_t simplex_idx>
struct _impl_degeneracies {
  using set = typename simpset::template Set<n>;
  using simplex =
      typename set::template materialize<(typename set::_)simplex_idx>::type;
  static constexpr bool value =
      (_simplex_degeneracies<n, simplex, simpset>())
          ? _impl_degeneracies<n, simpset, simplex_idx - 1>::value
          : false;
};

template <size_t n, typename simpset>
struct _impl_degeneracies<n, simpset, 0> {
  using set = typename simpset::template Set<n>;
  using simplex = typename set::template materialize<(typename set::_)0>::type;
  static constexpr bool value = _simplex_degeneracies<n, simplex, simpset>();
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
requires(condition_i::_proper_dimensions<n, simpset>::value &&
             condition_ii::_codomains<n, simpset>::value &&
                 condition_iii::_degeneracies<n, simpset>::value)
struct _impl_identities {
  static constexpr bool value = _impl_identities<_dim, simpset, n + 1>::value;
};

template <size_t _dim, typename simpset>
requires(condition_i::_proper_dimensions<_dim, simpset>::value &&
             condition_ii::_codomains<_dim, simpset>::value &&
                 condition_iii::_degeneracies<_dim, simpset>::value)
struct _impl_identities<_dim, simpset, _dim> {
  static constexpr bool value = true;
};

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
template <size_t _dim, typename simpset>
struct identities {
  static constexpr bool value = _impl_identities<_dim, simpset, 0>::value;
};

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
      // but in reality, they will yield classes with
      // `static constexpr size_t ::value` fields to indicate the value
      // of the face.
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
  // TS::template Set<size_t>;
  // { typename TS::template Set<size_t> } -> _SimplexSetEnum;

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
        static constexpr Set<0>::_ value = Set<0>::_::A;
      };

      template <>
      struct face<1> {
        static constexpr Set<0>::_ value = Set<0>::_::B;
      };
    };

    struct _g_type {
      static constexpr size_t _dim = 1;

      template <size_t i>
      struct face;

      template <>
      struct face<0> {
        static constexpr Set<0>::_ value = Set<0>::_::B;
      };

      template <>
      struct face<1> {
        static constexpr Set<0>::_ value = Set<0>::_::C;
      };
    };

    struct _gf_type {
      static constexpr size_t _dim = 1;

      template <size_t i>
      struct face;

      template <>
      struct face<0> {
        static constexpr Set<0>::_ value = Set<0>::_::A;
      };

      template <>
      struct face<1> {
        static constexpr Set<0>::_ value = Set<0>::_::C;
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

    static constexpr size_t _n_primitives = 1;

    enum _ { gfcomp };

    // TODO: helper to create simplices of prior ones...

    struct _gf_comp_type {
      static constexpr size_t _dim = 2;

      template <size_t i>
      struct face;

      template <>
      struct face<0> {
        static constexpr Set<1>::_ value = Set<1>::_::f;
      };

      template <>
      struct face<1> {
        static constexpr Set<1>::_ value = Set<1>::_::g;
      };

      template <>
      struct face<2> {
        static constexpr Set<1>::_ value = Set<1>::_::gf;
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
// using testStandard2Simplex2Truncated = RequiresTruncated<2,
// Standard2Simplex>;

}  // namespace simpsets::tests

}  // namespace protos::enums

int main(int argc, char* argv[]) {
  std::cout << "compiled!" << std::endl;
  return 0;
}
