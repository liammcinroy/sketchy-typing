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

// template <Ext e>
// struct X {};

template <template<typename T> class TExt>
struct X {};

}  // namespace templates::nontypes

int main(int argc, char* argv[]) {
  std::cout << "compiled!" << std::endl;
  return 0;
}
