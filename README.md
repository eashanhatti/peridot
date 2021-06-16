# Clamn
Clamn is intended to be a functional systems language. It's mostly an experiment in pure functional language design that focuses on performance. Most functional languages are not particularly known for their performance. A major reason for this is the relatively high amount of abstraction used in functional code. Performance problems *can* be fixed by an optimizing compiler, however, this tends to be more of a band-aid. Ideally, we'd like to be able to reason about and control the performance of functional languages the same way we can with systems languages.

The main things I'm focusing on in Clamn are partial evaluation, data layout abstraction, and dependent types. Partial evaluation is compile time evaluation - everything that can be evaluated at compile time is. This concept eliminates some abstraction right off the bat by allowing us to express inlining. However, partial evaluation is very general and can also express more complicated concepts, such as removing the abstraction of an interpreter for a DSL by partially evaluating it on a statically known program (something that macros would typically be used for). Interacting with dependent types, it becomes even more useful. Monomorphization can be expressed as partially evaluating a function from types to values.

Dependent types are another extremely general feature, they allow us to express things like generics, tagged unions, and proofs. However, they also typically come with performance issues because they make the following question harder: What is the representation of some type at run time? For instance, what is the size of a value of type `if true then Int else String`? To alleviate this, we can allow for quantification and abstraction over data layouts - layouts are made a part of the type system. For instance, one way of doing this is to put the layout of a type on its kind. We can then add rules such as "a type may be given a kind with a layout greater than what it needs", reflecting the constraints that exist in reality. Data layout abstraction also interacts with partial evaluation - layouts must be able to be partially evaluated away.

Current Roadmap:
- [ ] Core language
    - [ ] Language
        - [x] Dependent functions
        - [x] Dependent pairs
        - [x] Opt-in lazy eval
        - [ ] Staging
        - [ ] Layout Polymorphism
        - [ ] External interaction/effects
            - [ ] `World`
            - [ ] Basic FFI 
    - [x] Typechecker
    - [x] Evaluator
    - [ ] Partial evaluation
        - [ ] Totality checking
- [ ] Surface language
    - [ ] Elaborator
    - [x] Modules
        - [x] Definitions
        - [x] Imports
    - [ ] Typing
        - [x] Dependent functions
        - [x] Dependent records
        - [ ] Staging
        - [ ] Layout Polymorphism
        - [ ] Basic type inference
    - [ ] Pattern matching
    - [ ] External interaction/effects
        - [ ] `World`
        - [ ] Basic FFI
- [ ] Backend
    - [ ] Simple codegen
