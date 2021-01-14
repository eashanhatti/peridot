# Clamn

Clamn is intended to be a functional systems language. My motivation behind the project is the desire to have a pure functional language that provides the performance and performance *guarantees* of systems languages like Rust, C++, and D. Idiomatic functional code should be able to be written without sacrificing performance

Major Desired Features:
* A zero-cost effect system along with effect inference
* Tracking of and polymorphism over data layout to allow for easy handling of unboxed data. This will be useful for compiling dependent types, where the layout of the data is not always known statically
* Region based memory management
* A staging system. Useful for guaranteeing monomorphization/inlining, expressing external code, and partial evaluation

Purity is very useful, both in the theoretical foundations of a language and for people actually using the language, but it shouldn't be a burden. Use of effects, impure code, should involve zero friction, as impurity is often desired for performance or simply because the problem domain needs it. At the moment algebraic effects seem like the most likely route the language will go. Reiterating on the desire for zero friction, [Koka](https://github.com/koka-lang/koka)'s effect system is a very good example of what I have in mind, with polymorphism over and inference of effects. From the systems language angle, the effect system needs to be zero cost. Code written using effects should perform identically to the same code written an an impure language. The effect system should be fully erasable in the backend.