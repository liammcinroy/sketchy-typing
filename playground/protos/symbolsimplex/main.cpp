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
//     To be more concrete, suppose F_0(T, U) is T x U. then we might encode
//     F_0(T, U) within the 1-truncated (or is it 0-truncated) simplicial set
//     (p_T : T x U -> T, p_U : T x U -> U, 0) --- note that this might be
//     better represented as the left cone over the 2-2 horn over the terminal
//     object... see:
//     https://ncatlab.org/nlab/show/join+of+simplicial+sets
//     #joins_with_the_point_cones
//     Similarly, we'd have that T + U is the right cone over the 0-2 horn
//     from the initial object.
//
//     To generalize, for F_0(...), we just encode the 1-truncated simplicial
//     set of the vertices + any structural information we have about the
//     (co)limit diagram (if they exist).
//
//     If we don't have any sort of additional semantic information about
//     F_0(...), then we just don't have any n-simplexes for n > 0 encoding
//     as a witness of the introduced vertex. I.e. we revert to (1). But note
//     that this is just a special case of exhibiting a simplex, it's just a
//     0-simplex.
//
//     All of this is to say, (2) boils down to providing a parameterized
//     type taking a list symbols (for each 0-, 1-, etc... simplices involved)
//     and producing some simplicial set with the new simplices of interest.
//
//     Then, "verifying" the semantics is just confirming that all generated
//     symbols are valid, according to the specification.
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
concept _Symbol = (requires {
  // The unique tag --- note that
  requires(std::same_as<std::remove_const_t<decltype(s::tag)>,
                        typename s::TagType>);

  // The arity of its arguments
  { s::arity } -> std::same_as<const size_t>;
} &&
                   (
                       requires { s::arity == 0; } ||
                       requires {
                         // accessor to its arguments, if they exist
                         s::template arg<size_t>;

                         // append new symbols under the pack's
                         // `::type::symbol`. s::template <typename...>
                         // append::type::symbol;
                       }));

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

// Implements `_Symbol`
template <typename T, T _tag, typename... _args>
requires(details::boolevals::symbols::template are_symbols<
         _args...>::value) struct Symbol {
  using TagType = T;

  static constexpr T tag = _tag;

  static constexpr size_t arity = sizeof...(_args);

  template <size_t i>
  struct arg {
    using type = typename details::get::template at<i, _args...>::type;
  };

  template <typename new_arg0, typename... new_args>
  struct detailsappendtype {
    using symbol =
        typename Symbol<T, tag, _args..., typename new_arg0::type::symbol>::
            template detailsappendtype<new_args...>::symbol;
  };

  template <typename new_arg0>
  struct detailsappendtype<new_arg0> {
    using symbol = Symbol<T, tag, _args..., typename new_arg0::type::symbol>;
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
      using symbol = Symbol<T, _tag, _args...>;
    };
  };

  template <T _new_tag>
  using retag = Symbol<T, _new_tag, _args...>;
};

// Base case.
template <typename T, T _tag>
struct Symbol<T, _tag> {
  using TagType = T;

  static constexpr T tag = _tag;

  static constexpr size_t arity = 0;

  // Base case necessary here: we don't want to do this.
  // template <size_t i>
  // using arg = typename details::get::template at<i, _args...>::type;

  template <typename new_arg0, typename... new_args>
  struct detailsappendtype {
    using symbol = typename Symbol<T, tag, typename new_arg0::type::symbol>::
        template detailsappendtype<new_args...>::symbol;
  };

  template <typename new_arg0>
  struct detailsappendtype<new_arg0> {
    using symbol = Symbol<T, tag, typename new_arg0::type::symbol>;
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
      using symbol = Symbol<T, _tag>;
    };
  };
};

namespace tests::symbol {

template <typename symbol>
requires _Symbol<symbol>
struct RequiresSymbol {
};

template <size_t tag, typename... args>
using SymbolST = Symbol<size_t, tag, args...>;

using test0 = RequiresSymbol<SymbolST<0>>;
using test1 = RequiresSymbol<SymbolST<1, SymbolST<0>>>;

};  // namespace tests::symbol

//// Now we can get into the simplices.

template <size_t _dim, typename s>
concept _Simplex = (requires {
  // the dimension of the simplex.
  requires(s::dim == _dim);

  // the symbol attached to the simplex
  requires(_Symbol<typename s::symbol>);

  // we don't explicitly enforce that each degeneracy is a
  // `_Simplex` here. That will be handled in `Simplex`.
  // s::template degeneracy<size_t>;
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
  // another trick on the compiler, too many connectives in the `Simplex`
  // `requires` confuses it.
  static constexpr bool value =
      (n == 0) ? sizeof...(faces) == 0 : sizeof...(faces) == n + 1;
};

template <size_t n, typename... faces>
struct is_simplex {
  static constexpr bool value =
      dimension<n, faces...>::value && form_simplex<n, true, faces...>::value;
};

}  // namespace details::boolevals::simplicial::faces

namespace details::boolevals::simplicial {

template <size_t n, typename simplex>
requires _Simplex<n, simplex>
struct form_simplex {
  template <typename... fs>
  struct sub_form_simplex {
    using type = typename faces::template form_simplex<n, true, fs...>;
  };

  static constexpr bool value =
      simplex::template apply_faces<sub_form_simplex>::value;
};

template <typename simplex>
requires _Simplex<0, simplex>
struct form_simplex<0, simplex> {
  static constexpr bool value = true;
};

template <size_t n, typename simplex>
requires _Simplex<n, simplex>
struct dimension {
  template <typename... fs>
  struct sub_dimension {
    using type = typename faces::template dimension<n, fs...>;
  };

  static constexpr bool value =
      simplex::template apply_faces<sub_dimension>::value;
};

template <typename simplex>
requires _Simplex<0, simplex>
struct dimension<0, simplex> {
  static constexpr bool value = true;
};

template <size_t n, typename simplex>
struct is_simplex {
  static constexpr bool value =
      dimension<n, simplex>::value && form_simplex<n, simplex>::value;
};

}  // namespace details::boolevals::simplicial

namespace details::simplicial {

enum _Conditions { Less, Id, Greater };

template <size_t i, size_t j>
constexpr _Conditions condition() {
  if (i < j) return _Conditions::Less;
  if (i == j || i == j + 1)
    return _Conditions::Id;
  else
    return _Conditions::Greater;
}

template <size_t i, size_t j, typename simplex, _Conditions cond>
struct degeneracy_impl;

template <size_t i, size_t j, typename simplex>
struct degeneracy_impl<i, j, simplex, _Conditions::Less> {
  using type =
      typename simplex::template face<i>::type::template degeneracy<j -
                                                                    1>::type;
};

template <size_t i, size_t j, typename simplex>
struct degeneracy_impl<i, j, simplex, _Conditions::Id> {
  using type = simplex;
};

template <size_t i, size_t j, typename simplex>
struct degeneracy_impl<i, j, simplex, _Conditions::Greater> {
  using type =
      typename simplex::template face<i -
                                      1>::type::template degeneracy<j>::type;
};

template <size_t j,
          typename simplex,
          template <typename...>
          typename constructor>
struct degeneracy {
  template <size_t N, typename = std::make_index_sequence<N>>
  struct build;

  template <size_t N, size_t... S>
  struct build<N, std::index_sequence<S...>> {
    template <size_t i>
    using face =
        typename degeneracy_impl<i, j, simplex, condition<i, j>()>::type;

    using type = typename constructor<face<S>...>::type;
  };

  using type = typename build<simplex::dim + 2>::type;
};

}  // namespace details::simplicial

// Implements _Simplex<sizeof...(faces) + 1>.
template <_Symbol _symbol, size_t n, typename... faces>
requires(details::boolevals::simplicial::faces::is_simplex<n, faces...>::
             value) struct Simplex {
  using This = Simplex<_symbol, n, faces...>;

  static constexpr size_t dim = n;

  using symbol = _symbol;

  template <size_t i>
  using face = typename details::get::template at<i, faces...>;

  template <template <typename...> typename F>
  using apply_faces = typename F<faces...>::type;

  template <size_t j>
  struct degeneracy {
    template <typename... new_faces>
    struct new_degenerate_simplex {
      using type = Simplex<_symbol, n + 1, new_faces...>;
    };

    using type = typename details::simplicial::
        degeneracy<j, This, new_degenerate_simplex>::type;
  };
};

template <_Symbol _symbol>
struct Simplex<_symbol, 0> {
  using This = Simplex<_symbol, 0>;

  static constexpr size_t dim = 0;

  using symbol = _symbol;

  template <size_t>
  struct degeneracy {
    using type = Simplex<_symbol, 1, This, This>;
  };
};

namespace tests::simplex {
template <size_t tag, typename... args>
using SymbolST = Symbol<size_t, tag, args...>;

template <size_t n, typename simplex>
requires _Simplex<n, simplex>
struct RequiresSimplex {
};

template <_Symbol _symbol, size_t n, typename... faces>
using SimplexST = Simplex<_symbol, n, faces...>;

using S0_0 = SimplexST<SymbolST<0>, 0>;
using test0 = RequiresSimplex<0, S0_0>;

// this is a degenerate 1-simplex (actually a vertex)
using DS1 = SimplexST<SymbolST<0>, 1, S0_0, S0_0>;
using test1 = RequiresSimplex<1, DS1>;
// see!
static_assert(std::same_as<DS1, typename S0_0::degeneracy<0>::type>);

// this is a degenerate 2-simplex (actually a vertex)
using DS2 = SimplexST<SymbolST<0>, 2, DS1, DS1, DS1>;
using test2 = RequiresSimplex<2, DS2>;
// see!
static_assert(std::same_as<DS2, typename DS1::degeneracy<0>::type>);
static_assert(std::same_as<DS2, typename DS1::degeneracy<1>::type>);

using S0_1 = SimplexST<SymbolST<1>, 0>;
using S0_2 = SimplexST<SymbolST<2>, 0>;

using S1_0 = SimplexST<SymbolST<12>, 1, S0_1, S0_2>;
using S1_1 = SimplexST<SymbolST<02>, 1, S0_0, S0_2>;
using S1_2 = SimplexST<SymbolST<01>, 1, S0_0, S0_1>;

// this is a standard 2-simplex
using S2 = SimplexST<SymbolST<0x012>, 2, S1_2, S1_1, S1_0>;
using test3 = RequiresSimplex<2, S2>;

// try opposite
// using opS2 = S2;  // OpSimplex<2, S2>;
// using test4 = RequiresSimplex<2, opS2>;

};  // namespace tests::simplex

//// now we can get into the simplicial sets.

// first, some helpers for determining when/whether things are simplices

namespace details::boolevals::simplicial {

template <typename simplex, typename... simplices>
requires(is_simplex<simplex::dim, simplex>::value) struct are_simplices_impl {
  static constexpr bool value = are_simplices_impl<simplices...>::value;
};

template <typename simplex>
requires(is_simplex<simplex::dim,
                    simplex>::value) struct are_simplices_impl<simplex> {
  static constexpr bool value = true;
};

template <typename... simplices>
struct are_simplices {
  static constexpr bool value = are_simplices_impl<simplices...>::value;
};

template <>
struct are_simplices<> {
  static constexpr bool value = true;
};

}  // namespace details::boolevals::simplicial

// now, some helpers for relabeling simplices...

namespace details::simplicial {

template <size_t n, typename simplex, template <_Symbol> typename labeler>
struct relabel_impl {
  template <_Symbol _symbol, typename... new_faces>
  struct sub_constructor {
    using type = Simplex<typename labeler<_symbol>::type, n - 1, new_faces...>;
  };
};

// technically, a simplicial map would have to respect the dimensional
// structure (i.e. saying n-simplex to point is really n-simplex to the
// n-fold degeneracy of the point).
//
// so, since the structure is duplicated throughout simplices, dependent
// only on the `_Symbol`s, then this is really just relabeling simplices!
//
// But note, that for implementation details, it can be useful to know the
// sequence of face maps applied during the application, e.g. in `op`.
//

template <template <_Symbol> typename map,
          typename simplex,
          size_t N,
          typename = std::make_index_sequence<N>>
struct apply_simplicial_map_impl;

template <template <_Symbol> typename map,
          typename simplex,
          size_t N,
          size_t... S>
struct apply_simplicial_map_impl<map, simplex, N, std::index_sequence<S...>> {
  template <size_t i>
  struct new_face {
    using type = typename apply_simplicial_map_impl<
        map,
        typename simplex::template face<i>::type,
        simplex::dim>::type;
  };

  using type = Simplex<typename map<typename simplex::symbol>::type,
                       simplex::dim,
                       typename new_face<S>::type...>;
};

// Base case N = 1:

template <template <_Symbol> typename map, typename simplex>
struct apply_simplicial_map_impl<map, simplex, 1, std::index_sequence<0>> {
  using type =
      Simplex<typename map<typename simplex::symbol>::type, simplex::dim>;
};

}  // namespace details::simplicial

template <template <_Symbol> typename map, typename simplex>
requires(details::boolevals::simplicial::are_simplices<
         simplex>::value) using apply_simplicial_map =
    typename details::simplicial::
        apply_simplicial_map_impl<map, simplex, simplex::dim + 1>::type;

namespace tests::simplex::maps {

template <_Symbol>
struct BasicMap1;

template <>
struct BasicMap1<SymbolST<0>> {
  using type = SymbolST<1>;
};

using MS0_0 = apply_simplicial_map<BasicMap1, S0_0>;
static_assert(std::same_as<MS0_0, SimplexST<SymbolST<1>, 0>>);

}  // namespace tests::simplex::maps

namespace details::simplicial {

template <size_t n, typename simplex>
requires(details::boolevals::simplicial::is_simplex<n, simplex>::
             value) struct OpSimplex {
  using This = OpSimplex<n, simplex>;

  static constexpr size_t dim = n;

  using symbol = typename simplex::symbol;

  template <size_t i>
  struct face {
    using type =
        OpSimplex<n - 1, typename simplex::template face<dim - i>::type>;
  };

  template <template <typename...> typename F,
            size_t N,
            typename = std::make_index_sequence<N>>
  struct apply_faces_impl;

  template <template <typename...> typename F, size_t N, size_t... S>
  struct apply_faces_impl<F, N, std::index_sequence<S...>> {
    using type = typename F<typename face<S>::type...>::type;
  };

  template <template <typename...> typename F>
  using apply_faces = typename apply_faces_impl<F, n + 1>::type;

  template <size_t j>
  struct degeneracy {
    using type =
        OpSimplex<n - 1, typename simplex::template degeneracy<dim - j>::type>;
  };
};

template <typename simplex>
struct OpSimplex<0, simplex> {
  using This = OpSimplex<0, simplex>;

  static constexpr size_t dim = 0;

  using symbol = typename simplex::_symbol;

  template <size_t j>
  struct degeneracy {
    using type =
        OpSimplex<1, typename simplex::template degeneracy<dim - j>::type>;
  };
};

// I think we don't need to use `OpSimplex` to find the correct symbol, since
// the simplicial identities imply that any labels should be consistent
// across... don't have a formal proof of the fact, but empirically it seems
// to work for simplices. Maybe not for simplicial sets or degenerates....

template <size_t n, typename simplex>
struct op_impl {
  template <_Symbol symbol, size_t i, bool match>
  struct op_map_impl;

  template <_Symbol symbol, size_t i>
  struct op_map_impl<symbol, i, true> {
    using type = typename simplex::template face<n - i>::type::symbol;
  };

  template <_Symbol symbol, size_t i>
  struct op_map_impl<symbol, i, false> {
    using type =
        typename op_map_impl<symbol,
                             i + 1,
                             std::same_as<symbol,
                                          typename simplex::template face<
                                              i + 1>::type::symbol>>::type;
  };

  template <_Symbol symbol>
  struct op_map_impl<symbol, n, true> {
    using type = typename simplex::template face<0>::type::symbol;
  };

  template <_Symbol symbol>
  struct op_map_impl<symbol, n, false> {
    using type =
        typename op_impl<n - 1, typename simplex::template face<0>::type>::
            template op_map<symbol>::type;
  };

  template <_Symbol symbol>
  struct op_map {
    using type = typename op_map_impl<
        symbol,
        0,
        std::same_as<symbol,
                     typename simplex::template face<0>::type::symbol>>::type;
  };

  template <>
  struct op_map<typename simplex::symbol> {
    using type = typename simplex::symbol;
  };

  // would be nice to do this, but alas not used as not deducible...
  // template <size_t i>
  // struct OpMap<typename simplex::template face<i>::type::symbol> {
  //   using type =
  //       typename simplex::template face<simplex::dim - i>::type::symbol;
  // };

  using type = apply_simplicial_map<op_map, simplex>;
};

template <typename simplex>
struct op_impl<0, simplex> {
  template <_Symbol symbol>
  struct op_map;

  template <>
  struct op_map<typename simplex::symbol> {
    using type = typename simplex::symbol;
  };

  using type = Simplex<typename simplex::symbol, 0>;
};

}  // namespace details::simplicial

template <typename simplex>
requires(
    details::boolevals::simplicial::are_simplices<simplex>::value) using op =
    typename details::simplicial::op_impl<simplex::dim, simplex>::type;

namespace tests::simplex {

// try opposite

static_assert(std::same_as<S0_0, op<S0_0>>);

using opS1_0 = op<S1_0>;
static_assert(std::same_as<SimplexST<SymbolST<12>, 1, S0_2, S0_1>, opS1_0>);

using opS2 = op<S2>;  // OpSimplex<2, S2>;
using test4 = RequiresSimplex<2, opS2>;

}  // namespace tests::simplex

//// now (co)cones

namespace details::simplicial {

template <_Symbol cone_sym,
          typename simplex,
          size_t N,
          typename = std::make_index_sequence<N>>
struct cone_impl;

template <_Symbol cone_sym, typename simplex, size_t N, size_t... S>
struct cone_impl<cone_sym, simplex, N, std::index_sequence<S...>> {
  template <size_t i>
  struct new_face {
    using type = typename cone_impl<cone_sym,
                                    typename simplex::template face<i>::type,
                                    simplex::dim>::type;
  };

  using type = Simplex<cone_sym,
                       simplex::dim + 1,
                       typename new_face<S>::type...,
                       simplex>;
};

// Base case N = 1:

template <_Symbol cone_sym, typename simplex>
struct cone_impl<cone_sym, simplex, 1, std::index_sequence<0>> {
  using type =
      Simplex<cone_sym, simplex::dim + 1, Simplex<cone_sym, 0>, simplex>;
};

}  // namespace details::simplicial

template <_Symbol cone_sym, typename simplex>
using cone = typename details::simplicial::
    cone_impl<cone_sym, simplex, simplex::dim + 1>::type;

namespace details::simplicial {

template <_Symbol cone_sym,
          typename simplex,
          size_t N,
          typename = std::make_index_sequence<N>>
struct cocone_impl;

template <_Symbol cone_sym, typename simplex, size_t N, size_t... S>
struct cocone_impl<cone_sym, simplex, N, std::index_sequence<S...>> {
  template <size_t i>
  struct new_face {
    using type = typename cocone_impl<cone_sym,
                                    typename simplex::template face<i>::type,
                                    simplex::dim>::type;
  };

  using type = Simplex<cone_sym,
                       simplex::dim + 1,
                       simplex,
                       typename new_face<S>::type...>;
};

// Base case N = 1:

template <_Symbol cone_sym, typename simplex>
struct cocone_impl<cone_sym, simplex, 1, std::index_sequence<0>> {
  using type =
      Simplex<cone_sym, simplex::dim + 1, simplex, Simplex<cone_sym, 0>>;
};

}  // namespace details::simplicial

template <_Symbol cone_sym, typename simplex>
using cocone = typename details::simplicial::
    cocone_impl<cone_sym, simplex, simplex::dim + 1>::type;

namespace tests::simplex::cones {

// base case
static_assert(std::same_as<DS1, cone<SymbolST<0>, S0_0>>);
static_assert(std::same_as<DS1, cocone<SymbolST<0>, S0_0>>);

// iterated
static_assert(std::same_as<DS2, cone<SymbolST<0>, DS1>>);
static_assert(std::same_as<DS2, cocone<SymbolST<0>, DS1>>);

}  // namespace tests::simplex::cones

// now we'll give some examples of formation simplicial maps...

namespace tests::simplex::form {

// template <_Symbol

}

// we don't ask to specifically enumerate all of the simplices of
// a simplicial set, instead we adopt the convention that there are
// is a collection of `TagType`s for primitives at each dimension
// and a collection of `_DiagramSimplicialSet` for formations at each
// dimension.
//
// Notably, the formation `_DiagramSimplicialSet`s are fully enumerable, and
// ought to include the proper `_Symbol` for the formed simplices. We might
// implement `Limit<...>` and `Colimit<...>` methods

template <size_t _dim, typename sc>
concept _DiagramSimplexComponent = requires {
  requires(sc::dim == _dim);

  // the number of simplices.
  { sc::count } -> std::same_as<const size_t>;

  // iterate, through the count.
  sc::template iterate<size_t>;

  // lower component.
  typename sc::lower;
};

template <size_t _dim, typename s>
concept _DiagramSimplicialSet = requires {
  requires(s::dim == _dim);
};

/*
template <size_t _dim, typename s>
concept _SimplicialSet = requires {
};
*/

// template <typename s>
// concept _SimplicialSet = requires {
//   // test for membership
//   s:template is_member<typename>;
//
//   // again, not ideal but would want:
//   // typename SS::template is_member<_Symbol>;
//
//   // this would be nice, but oh well
//   // { SS::is_member<_Symbol>::value } -> std::same_as<const bool>;
// };

//// it seems like there's less and less we can enforce with `concept`s
//// alone at this point, so now we'll just make some helpers?

namespace tests::formation {}

}  // namespace simpsets

}  // namespace protos::symbolsimplex

int main(int argc, char* argv[]) {
  std::cout << "S2 symbols: "
            << protos::symbolsimplex::simpsets::tests::simplex::S2::symbol::tag
            << "("
            << protos::symbolsimplex::simpsets::tests::simplex::S2::face<
                   0>::type::symbol::tag
            << ", "
            << protos::symbolsimplex::simpsets::tests::simplex::S2::face<
                   1>::type::symbol::tag
            << ", "
            << protos::symbolsimplex::simpsets::tests::simplex::S2::face<
                   2>::type::symbol::tag
            << ")" << std::endl;
  std::cout
      << "opS2 symbols: "
      << protos::symbolsimplex::simpsets::tests::simplex::opS2::symbol::tag
      << "("
      << protos::symbolsimplex::simpsets::tests::simplex::opS2::face<
             0>::type::symbol::tag
      << ", "
      << protos::symbolsimplex::simpsets::tests::simplex::opS2::face<
             1>::type::symbol::tag
      << ", "
      << protos::symbolsimplex::simpsets::tests::simplex::opS2::face<
             2>::type::symbol::tag
      << ")" << std::endl;
  std::cout << "compiled!" << std::endl;
  return 0;
}
