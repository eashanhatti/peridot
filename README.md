An experimental language for exploring the practical applications of two level type theory.

Discussion takes place on the [r/ProgrammingLanguages Discord server](https://discord.gg/jFZ8JyUNtn) in the #peridot channel.

**Note**: Peridot is a proof-of-concept! Don't use it for anything serious.

### References and Inspiration

* [REFERENCES.md](./REFERENCES.md): A list of prior art that have influenced Peridot's design and implementation in major ways

### Information

* [OLD_VS_NEW.md](./notes/OLD_VS_NEW.md): A comparison of Peridot and [Konna](https://github.com/eashanhatti/konna), a previous project of mine also based on 2LTT

### Introduction

High-level programming and program performance are at odds. High-level languages enable complex, pervasive abstractions, whereas high performance demands these abstractions be reduced to a minimum. Thus, an optimizing compiler is an essential part of a high-level language that seeks to accomplish both goals. However, even the most sophisticated optimizer can fall short when presented with abstraction it was not built to deal with. As programmers develop new abstractions, a choice must be made between the following options:

1. Augmenting the optimizer to deal with these new abstractions
2. Abandoning performance in exchange for high-level programming
3. Abandoning high-level programming in exchange for performance

Option 1 is the most attractive, as it would allow our programs to be both high-level and high-performance. Options 2 and 3 are not attractive, since we have to abandon one of the two. However, option 1 has shortcomings too! It is impractical to augment the optimizer every time a new library is developed, this would result in the compiler becoming extremely bloated. Furthermore, this forces compiler developers to have the necessary know-how to implement optimizations for a library. Ideally, the library developers themselves would be the only ones who need to have this knowledge. Taking all of this into account, it makes sense why, despite their shortcomings, options 2 and 3 are often chosen. Option 1 would be extremely valuable, but it is also costly to implement.

Peridot is an experimental language which attempts to eliminate the shortcomings of option 1 by allowing the entire compiler backend can be implemented in userspace. The compiler does not implement any built-in backend functionality at all. Every transformation and optimization in the backend pipeline -- CPS translation, inlining, monomorphization, constant folding, fusion, strictness analysis, etc -- can be implemented in userspace via metaprogramming. Library authors can easily implement the domain-specific optimizations they need, backend components become modular, and the compiler avoids bloat.

Peridot's basis lies in λProlog and two-level type theory (2LTT). It is a two-level language, one level supporting typed logic programming with pattern unification, the other level supporting lazy dependently typed functional programming, with the first used to metaprogram the second. The language's basis in 2LTT allows it to cleanly separate these two levels using types -- it is essentially two languages that look and feel like one language. With regard to implementing a compiler backend, the language's basis in λProlog allows metaprograms to be written declaratively, avoid issues such as the phase-ordering problem, deal with variable binding easily, automatically expose equalities between programs, be easily extensible, etc.
