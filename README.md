# Sketchy Typing

### Playground Prototypes

The history of prototypes is roughly:

- [`protos::enums`](playground/protos/enums): fully enumerated simplicial
sets only.

- [`protos::limits`](playground/protos/limits): building towards maps, limits,
cones. Fully enumerated as in `protos::enums`, so major issues.

- [`protos::symbolsimplex`](playground/protos/symbolsimplex): introduction of
`_Symbol`s, better model for constructing `Simplex`es, no longer fully
enumerable so better maps, limits, cones.

In any of these playgrounds, the `build` file will build `main.cpp` using
`g++ --std=c++20` to `main.out`.

There are other playgrounds to explore, most contain fragments of playing
with `concept`s or `template`s functionality in C++20.

### Setup

TODO once a self contained project

### Project Structure

Eventually:

- follow the "canonical project structure" suggested
[here](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2018/p1204r0.html).

- follow the "boost `template` guidelines" suggested
[here](https://www.boost.org/development/int_const_guidelines.html).

- follow the "ISO `concept`s best practices" suggested
[here](https://github.com/isocpp/CppCoreGuidelines/blob/master/CppCoreGuidelines.md).

- add documentation, motivations, etc.

