An experimental language for exploring the practical applications of two level type theory.

Discussion takes place on the [r/ProgrammingLanguages Discord server](https://discord.gg/jFZ8JyUNtn) in the #peridot channel.

### References and Inspiration

* [REFERENCES.md](./REFERENCES.md): A list of prior art that have influenced Peridot's design and implementation in major ways

### Information

* [OLD_VS_NEW.md](./notes/OLD_VS_NEW.md): A comparison of Peridot and [Konna](https://github.com/eashanhatti/konna), a previous project of mine also based on 2LTT

### Introduction

High-level programming and program performance are at odds. High-level languages enable complex, pervasive abstractions, whereas high performance demands these abstractions be reduced to a minimum. Thus, an optimizing compiler is an essential part of a high-level language that seeks to accomplish both goals. However, even the most sophisticated optimizer can fall short when presented with abstraction it was not built to deal with. As programmers develop new abstractions, a choice must be made:

1. Augmenting the optimizer to deal with these new abstractions
2. Accepting subpar performance
3. Abandoning abstraction and programming in a low-level style

Options 2 and 3 are not ideal, since we have to abandon high-level programming or high performance. However, option 1 is not ideal either! Abstractions developed by users can be developed far faster than the optimizer can be augmented. Furthermore, option 1 requires compiler developers to be familiar with the abstractions that require optimization - ideally, the programmers implementing these abstractions would be the only ones required to have this knowledge. Taking all of this into account, it makes sense why options 2 and 3 are often the chosen options. Domain-specific optimizations are extremely valuable, but also costly to implement.

Peridot is a language designed to enable option 1: the entire compiler backend can be implemented in userspace via metaprogramming. In fact, the compiler does not implement any built-in backend functionality at all - the optimizer can easily be augmented by users because it is entirely implemented by users in the first place. The metaprogramming fragment of the language is based upon λProlog - it supports typed logic programming with higher-order abstract syntax (HOAS). The choice of logic programming allows metaprograms to be implemented declaratively and easily extended, and use of HOAS frees programmers from managing binding structure (which can be error-prone otherwise). This also means that metaprograms can only produce well-scoped code. Furthermore, metaprograms must preserve typing - they also only produce well-typed code.

The “object” fragment - the fragment manipulated by metaprograms - is pure (except for nontermination), dependently typed, and functional. Peridot is a two-level language: these two fragments - despite being very distinct - are tightly integrated together into one system.
