#include <concepts>
#include <iostream>

namespace concepts::basic {

template <typename T>
concept HasType = requires {
  T::type;
};

}  // namespace concepts::basic

int main(int argc, char* argv[]) {
  std::cout << "compiled!" << std::endl;
  return 0;
}
