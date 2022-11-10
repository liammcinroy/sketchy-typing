#include <algorithm>
#include <iostream>
#include <type_traits>

namespace templates::str {

// I want to be able to do like
// enable_if_t<str1 == str2> in templates

template <size_t n>
struct string {
  constexpr string(const char (&val)[n]) { std::copy_n(val, n, _value); }

  char _value[n];

  auto operator<=>(const string&) const = default;
};

// class deduction guide

// template <string str1, string str2, typename T>
// using str_equal_enable_t = typename std::enable_if_t<str1 == str2, T>;

// with https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2018/p0732r2.pdf
// it'd be easy to do
//
// template <size_t n>
// string(const char[n]) -> string<n>;
//
// template <string str1>
// void f() {}
//
// instead, we have to do the annoying

template <size_t n, string<n> str1>
void f() {}

// trying out some explicit stuff
// template <>
// string(const char str[]) -> string<sizeof(str)>;

template <size_t n1,       size_t n2,
          string<n1> str1, string<n2> str2,
          typename T>
using str_eq_t = std::enable_if_t<str1 == str2, T>;

}  // namespace templates::str

int main(int argc, char* argv[]) {
  std::cout << "compiled!" << std::endl;
  return 0;
}
