#include <algorithm>
#include <compare>
#include <concepts>
#include <iostream>
#include <string>
#include <type_traits>

namespace protos::symbolsimplex {

// now, we are going to distill a simplicial set down to just its
// "symbolic" representation... i.e. we don't worry about actual types,
// etc. until the model enters the picture.
//
// to say a bit more, we'll have "primitives" the same as before, but
// we'll also allow tagging simplices with formations.
//
// So in some sense, we are specifying the signatures of the form:
// T, U ::= P0 | P1 | ... | F_0(T1, ...) | ...
//   where F_i are formation terms, and P0 | P1 | ... are the primitives.
//
// then function primitives are
// f, g ::= f_0(T) -> U | ...
//   where T, U are types in the previous sense.
//
// To explain how this gets translated into the simplicial structure, we
// will bootstrap the "enumerated simplicial sets" of `protos::enums`, where
// all of the simplices are enumerate.
//
// There, we support only Pi and f_k(P_i) -> P_j, or similarly enumerated
// terms. i.e. just primitive types, and arity 1 function primitives.
// There we had explicit underlying types for Pi etc., but we no longer require
// that in this namespace. I.e. we will just assign a `size_t` tag to each
// primitive (i.e. a symbol). Then a 0-simplex is just determined by its
// `size_t` tag, a 1-simplex is determined by its `size_t` tag and faces' tags,
// so on and so forth.
//
// To explain how we will allow for type formations, we can take two
// approaches.
//   1) allow T, U ::= F_0(...) | ... terms to inhabit the 0-simplices, via
//     tagging each formation as a symbol, and assigning the symbol of the
//     formed type as the symbol resulting from it applied to its arguments'
//     symbols.
//
//     This approach encodes no information about F_0(T, U)'s relation to
//     T, U in the 0-simplices or 1-simplices or anything.
//
//   2) provide some map of simplicial sets, parameterized by the arguments
//     to the type formation, which forms the new types and its related maps.
//
//     This approach encode information about F_0(T, U)'s relation to
//     T, U in the 1-simplices, and also 2-simplices if through a universal
//     property.
//
//     If there aren't any maps between F_0(T, U) and T, U (or we don't supply
//     a universal property), then this just becomes a new 0-simplex without
//     any relations in higher simplices.
//
// (1) is perhaps initially easier to implement, but runs into the same
// enumeration problem at higher simplices that we are facing currently.
//
// (2) on the other hand would allow for more advanced features in the future.
// for instance, this is how we would encode things in the homotopy n-cats.
//
// Then also note that (2) allows a potentially easy way to "rewrite"
// differently named models of a theory to another, etc., since everything
// is symbolic.
//
// The downside of (2) is that now we have to implement a symbol mechanism.
// However, it's relatively simple.

namespace simpsets {

template <typename s>
concept _Symbol = requires {
  // The unique tag --- note that
  { s::tag } -> std::same_as<const size_t>;

  // The arity of its arguments
  { s::arity } -> std::same_as<const size_t>;

  // accessor to its arguments
  // s::template arg<size_t>;

  // append new symbols under the pack's `::type::symbol`.
  // s::template <typename...> append::type::symbol;
};

namespace details {

//// Basic usual index variadic
namespace get {
template <size_t i, typename T0, typename... Ts>
struct f {
  using type = typename f<i - 1, Ts...>::type;
};

template <typename T0, typename... Ts>
struct f<0, T0, Ts...> {
  using type = T0;
};

template <size_t i, typename... Ts>
struct at {
  using type = typename f<i, Ts...>::type;
};

}  // namespace get

namespace boolevals::symbols {

template <typename s0, typename... setc>
requires _Symbol<s0>
struct are_symbols_impl {
  static constexpr bool value = are_symbols_impl<setc...>::value;
};

template <typename s0>
requires _Symbol<s0>
struct are_symbols_impl<s0> {
  static constexpr bool value = true;
};

template <typename... symbols>
struct are_symbols {
  static constexpr bool value = are_symbols_impl<symbols...>::value;
};

template <>
struct are_symbols<> {
  static constexpr bool value = true;
};

}  // namespace boolevals::symbols

}  // namespace details

// Implements _Symbol
template <size_t _tag, typename... _args>
requires(details::boolevals::symbols::template are_symbols<
         _args...>::value) struct Symbol {
  static constexpr size_t tag = _tag;

  static constexpr size_t arity = sizeof...(_args);

  template <size_t i>
  struct arg {
    using type = typename details::get::template at<i, _args...>::type;
  };

  template <typename new_arg0, typename... new_args>
  struct detailsappendtype {
    using symbol =
        typename Symbol<tag, _args..., typename new_arg0::type::symbol>::
            template detailsappendtype<new_args...>::symbol;
  };

  template <typename new_arg0>
  struct detailsappendtype<new_arg0> {
    using symbol = Symbol<tag, _args..., typename new_arg0::type::symbol>;
  };

  // helper function to apply new args' `::type::symbol` to a tag.
  template <typename... new_args>
  struct append {
    struct type {
      using symbol = typename detailsappendtype<new_args...>::symbol;
    };
  };

  template <>
  struct append<> {
    struct type {
      using symbol = Symbol<_tag, _args...>;
    };
  };
};

template <size_t _tag>
struct Symbol<_tag> {
  static constexpr size_t tag = _tag;

  static constexpr size_t arity = 0;

  // template <size_t i>
  // using arg = typename details::get::template at<i, _args...>::type;

  template <typename new_arg0, typename... new_args>
  struct detailsappendtype {
    using symbol = typename Symbol<tag, typename new_arg0::type::symbol>::
        template detailsappendtype<new_args...>::symbol;
  };

  template <typename new_arg0>
  struct detailsappendtype<new_arg0> {
    using symbol = Symbol<tag, typename new_arg0::type::symbol>;
  };

  // helper function to apply new args' `::type::symbol` to a tag.
  template <typename... new_args>
  struct append {
    struct type {
      using symbol = typename detailsappendtype<new_args...>::symbol;
    };
  };

  template <>
  struct append<> {
    struct type {
      using symbol = Symbol<_tag>;
    };
  };
};

namespace tests::symbol {

template <typename symbol>
requires _Symbol<symbol>
struct RequiresSymbol {
};

using test0 = RequiresSymbol<Symbol<0>>;
using test1 = RequiresSymbol<Symbol<1, Symbol<0>>>;

};  // namespace tests::symbol

//// Now we can get into the simplices.

template <size_t _dim, typename s>
concept _Simplex = (requires {
  // the dimension of the simplex.
  requires(s::dim == _dim);

  // the symbol attached to the simplex
  requires(_Symbol<typename s::symbol>);
} &&
                    (
                        requires { _dim <= 0; } ||
                        requires {
                          // we don't explicitly enforce that each face is a
                          // `_Simplex` here. That will be handled in
                          // `Simplex`.
                          s::template face<size_t>;

                          // helpers to apply to faces
                          // s::template apply_to_faces<template <typename...>
                          // class>;
                        }));

namespace details::boolevals::simplicial::faces {

template <size_t n, size_t i, size_t j, typename... faces>
requires(std::same_as<
         typename get::template at<j, faces...>::type::template face<i>::type,
         typename get::template at<i, faces...>::type::template face<
             j - 1>::type>) struct has_simplex_faces_impl {
  static constexpr size_t newi = (i > 0) ? i - 1 : j - 2;
  static constexpr size_t newj = (i > 0) ? j : j - 1;
  static constexpr bool value =
      has_simplex_faces_impl<n, newi, newj, faces...>::value;
};

template <size_t n, typename... faces>
requires(std::same_as<
         typename get::template at<1, faces...>::type::template face<0>::type,
         typename get::template at<0, faces...>::type::template face<
             0>::type>) struct has_simplex_faces_impl<n, 0, 1, faces...> {
  static constexpr bool value = true;
};

template <size_t n, typename... faces>
constexpr bool has_simplex_faces() {
  return has_simplex_faces_impl<n, n - 1, n, faces...>::value;
}

template <size_t n, bool hasfaces, typename... faces>
struct form_simplex;

// Base cases: n = 0 or 1, we just check if `_Simplex`, not `has_simplex_faces`
// we may safely assume `hasfaces` is passed as `true` to these, since it
// would not enumerate as `false` in any other specialization.

template <typename face0, typename... faces>
requires _Simplex<0, face0>
struct form_simplex<1, true, face0, faces...> {
  static constexpr bool value = form_simplex<1, true, faces...>::value;
};

template <typename face0>
requires _Simplex<0, face0>
struct form_simplex<1, true, face0> {
  static constexpr bool value = true;
};

template <bool hasfaces, typename... faces>
struct form_simplex<0, hasfaces, faces...> {
  static constexpr bool value = true;
};

template <size_t n, typename face0, typename... faces>
requires _Simplex<n - 1, face0>
struct form_simplex<n, true, face0, faces...> {
  template <typename... subfaces>
  struct sub_form_simplex {
    using type = form_simplex<n - 1, true, subfaces...>;
  };

  // we have to trick the compiler a little, since it'll test the
  // requirements for the partial specialization if we put this in
  // the requirements clause. But it won't if we put it here (at least,
  // until we need it)!
  static constexpr bool value =
      (has_simplex_faces<n, face0, faces...>())
          ? form_simplex<n, false, faces...>::value &&
                face0::template apply_faces<sub_form_simplex>::value
          : false;
};

template <size_t n, typename face0, typename... faces>
requires _Simplex<n - 1, face0>
struct form_simplex<n, false, face0, faces...> {
  template <typename... subfaces>
  struct sub_form_simplex {
    using type = form_simplex<n - 1, true, subfaces...>;
  };

  static constexpr bool value =
      form_simplex<n, false, faces...>::value &&
      face0::template apply_faces<sub_form_simplex>::value;
};

template <size_t n, typename face0>
requires _Simplex<n - 1, face0>
struct form_simplex<n, false, face0> {
  template <typename... subfaces>
  struct sub_form_simplex {
    using type = form_simplex<n - 1, true, subfaces...>;
  };

  static constexpr bool value =
      face0::template apply_faces<sub_form_simplex>::value;
};

template <size_t n, typename... faces>
struct dimension {
  static constexpr bool value =
      (n == 0) ? sizeof...(faces) == 0 : sizeof...(faces) == n + 1;
};

}  // namespace details::boolevals::simplicial::faces

// Implements _Simplex<sizeof...(faces) + 1>.
template <_Symbol _symbol, size_t n, typename... faces>
requires(details::boolevals::simplicial::faces::dimension<n, faces...>::value&&
             details::boolevals::simplicial::faces::
                 form_simplex<n, true, faces...>::value) struct Simplex {
  static constexpr size_t dim = n;

  using symbol = _symbol;

  template <size_t i>
  using face = typename details::get::template at<i, faces...>;

  template <template <typename...> typename F>
  using apply_faces = typename F<faces...>::type;
};

template <_Symbol _symbol>
struct Simplex<_symbol, 0> {
  static constexpr size_t dim = 0;

  using symbol = _symbol;
};

namespace tests::simplex {

template <size_t n, typename simplex>
requires _Simplex<n, simplex>
struct RequiresSimplex {
};

using S0_0 = Simplex<Symbol<0>, 0>;
using test0 = RequiresSimplex<0, S0_0>;

using DS1 = Simplex<Symbol<1>, 1, S0_0, S0_0>;
using test1 = RequiresSimplex<1, DS1>;

using DS2 = Simplex<Symbol<2>, 2, DS1, DS1, DS1>;
using test2 = RequiresSimplex<2, DS2>;

using S0_1 = Simplex<Symbol<1>, 0>;
using S0_2 = Simplex<Symbol<2>, 0>;

using S1_0 = Simplex<Symbol<0>, 1, S0_1, S0_2>;
using S1_1 = Simplex<Symbol<1>, 1, S0_0, S0_2>;
using S1_2 = Simplex<Symbol<2>, 1, S0_0, S0_1>;

using S2 = Simplex<Symbol<0>, 2, S1_2, S1_1, S1_0>;

};  // namespace tests::simplex

//// now we can get into the simplicial sets

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

}  // namespace details::boolevals::simplicial

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

}  // namespace protos::symbolsimplex

int main(int argc, char* argv[]) {
  std::cout << "compiled!" << std::endl;
  return 0;
}
