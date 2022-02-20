# Konna's Rationale In-Depth

In high level languages, abstractions easy to create - for example, functional languages often allow abstractions to be defined entirely in userspace, e.g recursion schemes and algebraic effects in Haskell. However, high performance demands that we reduce use of these abstractions to a minimum. In order to have both, one needs an optimizing compiler that can recognize abstractions and reduce them to lower-level code. However, even this can fail when the optimizer encounters a user-written abstraction it was not built to deal with. As programmers develop new abstractions, a choice has to be made:
1. Augmenting the optimizer to deal with these new abstractions
2. Accepting subpar performance

#2 is not ideal. However, #1 is not either! One reason is that user abstractions can be developed at a far faster rate than the compiler can - it is too costly to augment the optimizer every time a new abstraction is developed. However, there is a far more important reason: Compiler writers do not necessarily have the domain-specific knowledge required! The people who know best how to optimize an abstraction are the people writing that abstraction in the first place. However, this highlights another problem: *Those* people do not necessarily know how to write an optimizer! Optimizers are tricky bits of code that require special attention to phase-ordering and the internals of the compiler, as well as knowledge of the language the compiler is written in. Both groups lack knowledge that they need to augment the compiler's optimizer.

Taking all of this into consideration, it makes sense why #2 is often the chosen option. Domain-specific optimizations are extremely valuable, but also hard to implement. Ideally, the language itself would allow optimizations to be expressed as declaratively as possible, in userspace. That way programmers could write optimizers without thinking about anything except the optimizations themselves. Konna is such a language!

Konna is a high level language that enables users to declaratively optimize their domain specific abstractions. It has two layers:
1. A pure, dependently typed, high-level functional language
2. A logic language with support for contextual types

The second layer is used as a metaprogramming language for the first. Logic programming allows optimizers to be written declaratively - only with regard to the optimizations themselves.