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
using DS1 = SimplexST<SymbolST<1>, 1, S0_0, S0_0>;
using test1 = RequiresSimplex<1, DS1>;

// this is a degenerate 2-simplex (actually a vertex)
using DS2 = SimplexST<SymbolST<2>, 2, DS1, DS1, DS1>;
using test2 = RequiresSimplex<2, DS2>;

using S0_1 = SimplexST<SymbolST<1>, 0>;
using S0_2 = SimplexST<SymbolST<2>, 0>;

using S1_0 = SimplexST<SymbolST<12>, 1, S0_1, S0_2>;
using S1_1 = SimplexST<SymbolST<02>, 1, S0_0, S0_2>;
using S1_2 = SimplexST<SymbolST<01>, 1, S0_0, S0_1>;

// this is a standard 2-simplex
using S2 = SimplexST<SymbolST<012>, 2, S1_2, S1_1, S1_0>;

};  // namespace tests::simplex

//// now we can get into the simplicial sets.

// template <typename F>
// concept _Formation = requires {
//   // it'd be nice if we could do this, but apparently not...
//   F::template materialize<auto>;
// };

// template <size_t _arity, typename F>
// concept _Formation = requires {
//   // this would also maybe be nice...
//   F::template materialize<_Symbol...>;
// };

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
  std::cout << "compiled!" << std::endl;
  return 0;
}
