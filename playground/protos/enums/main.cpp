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
namespace boolevals {
namespace simplicial {

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
//         (TODO: for non-primitives, this might get odd...).
//   (iii) We now know that the `S::face`s are well-defined, hence
//         we need only check the simplicial identities, i.e. for each
//         `0 <= i < j <= S::_dim` that
//         `TruncSimpSet<n - 1>::materialize<S::face<j>>::face<i> ==
//         `TruncSimpSet<n - 1>::materialize<S::face<i>>::face<j - 1>`.
template <size_t _dim, typename TruncSimpSet>
constexpr bool identities() {
  // TODO: link up
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
