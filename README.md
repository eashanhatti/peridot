# Clamn

Clamn is intended to be a functional systems language. My motivation behind the project is to have a pure functional language that provides the performance and performance *guarantees* of languages like Rust, C++, and D.

Major Planned Features:
* An effect system a la Koka along with effect inference
* Tracking of and polymorphism over data layout to allow for easy handling of unboxed data. This will be useful for compiling dependent types, where the layout of the data is not always known statically
* Region based memory management
* A staging system. Useful for guaranteeing monomorphization/inlining, expressing external code, and partial evaluation

The first feature, an effect system, is intended to make sure the pure aspect of the language is not a burden. Purity is very useful both in practice and as a quality of the foundation of a functional language. The pure functional style is however not always the best style. The ability to use mutation or other effects is sometimes needed either for performance or because it simply suits the problem better. Pure functional languages usually have effect systems, such as Haskell's use of monads/the `eff` package or Idris's `effects` package. The goal is to also make that effect system *easy to use*, hence the desire for inference. Koka's algebraic effect system is an example of this.