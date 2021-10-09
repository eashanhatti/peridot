# Konna

*Important note*: Konna is a WIP. Currently the language is missing structs, pattern matching, IO, etc. But here's the ideas anyway:

Konna is an experimental language for exploring the practical applications of two level type theory.

A common pattern in languages with performance as a goal is to have some features be compile time only ("static"). C++ templates for instance, eliminate the overhead of polymorphism by statically generating specialized versions of each templated definition. However, another common trend is for these compile time languages - at the start very simple - to accrue more and more features that interact in ad hoc ways, harming ergonomics.

The problem here is not with the idea itself, but rather the execution. These static languages aren't designed from the start to be *actual languages*. Konna has a static language and a runtime language, but the static language is fully featured from the start. The static language is dependently typed, pure, and can manipulate programs of the runtime language as data. In contrast, the runtime language is monomorphic and impure. The combination of these two allows features such as conditional compilation, templates, user-directed inlining, compile time evaluation, macros, and specialization of DSLs to be expressed very naturally.

### Other Projects

If you're interested in this area of language design, here's some projects exploring similar stuff. Check them out!

[Basil](https://github.com/basilTeam/basil), by [Elucent](https://github.com/elucent).
> Lisp dialect featuring highly flexible syntax, arbitrary compile-time evaluation, and static types!

[Spiral](https://github.com/mrakgr/The-Spiral-Language), by [Marko Grdinić](https://github.com/mrakgr).
> Functional language with intensional polymorphism and first-class staging.