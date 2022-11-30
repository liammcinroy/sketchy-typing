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

namespace simpsets {

template <typename WE>
concept _SimplexEnum = (
    requires {
      // the dimension of the simplicial set
      { WE::n } -> std::same_as<const size_t>;

      // the underlying `enum`
      requires(std::is_enum_v<typename WE::_>);

      // a type constructor for each `enum`, i.e. each of the
      // points in the simplicial set, provided the `constexpr enum` value.
      typename WE::template materialize<typename WE::_>;
    } &&
    requires(const WE s) {
      // we can't explicitly require that either `::_` is an `enum`, or
      // `::_` is a `_VertexEnum` (`concept`s cannot be self-referential),
      // so we just require that `::_` is an `enum` or has a `::_` of its own
      // (as a proxy).
      // Note that the template specializations ought to require this instead
      // (since those can then reference the dimension of the simplex).
      requires(WE::n == 0 || WE::n == WE::template materialize<s>::n + 1);
    });

}  // namespace simpsets

}  // namespace protos::enums

int main(int argc, char* argv[]) {
  std::cout << "compiled!" << std::endl;
  return 0;
}
