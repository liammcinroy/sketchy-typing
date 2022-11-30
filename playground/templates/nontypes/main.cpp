#include <iostream>

namespace templates::nontypes {

// Of https://en.cppreference.com/w/cpp/language/
// class_template_argument_deduction

template <typename T>
struct Ext {
  constexpr Ext(T) {}

  auto operator<=>(const Ext&) const = default;
};

template <typename T>
Ext(T) -> Ext<T>;

// requires templates
// template <Ext e>
// struct X1 {};

template <template<typename T> class TExt>
struct X2 {};

}  // namespace templates::nontypes

int main(int argc, char* argv[]) {
  std::cout << "compiled!" << std::endl;
  return 0;
}
