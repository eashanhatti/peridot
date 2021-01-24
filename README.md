# Clamn

Clamn is intended to be a functional systems language. My motivation behind the project is the desire to have a pure functional language that provides the performance and performance *guarantees* of systems languages like Rust, C++, and D. Idiomatic functional code should be able to be written without sacrificing performance.

Major Desired Features:
* An effect system along with effect inference
* Partial evaluation. Enables zero-cost abstractions, allowing one to guarantee inlining/monomorphization as well as allowing one to have a subset of semantic macros
* Tracking of and polymorphism over data layout to allow for easy handling of unboxed data. This will be useful for compiling dependent types, where the layout of the data is not always known statically
* Region based memory management

Purity is very useful, both in the theoretical foundations of a language and for people actually using the language, but it shouldn't be a burden. Use of effects, impure code, should involve zero friction, as impurity is often desired for performance or simply the problem is more easily expressed using it. At the moment algebraic effects seem like the most likely route the language will go. Reiterating on the desire for zero friction, [Koka](https://github.com/koka-lang/koka)'s effect system is a very good example of what I have in mind, with polymorphism over and inference of effects. From the systems language angle, the effect system needs to be zero cost. Code written using effects should perform identically to the same code written an an impure language. The effect system should be fully erasable in the backend.

Most languages employ optimizations like inlining, monomorphization, specialization, etc. These are particularly important for performance in functional languages because of the heavy use of polymorphism and higher order functions. However, for this language it is also important that these be controllable by the user in order to be performance guarantees. Partial evaluation is a generalization of all the above optimizations, allowing us to have all of them with only one feature. For instance, inlining is the partial evaluation of function application. Using a single feature to implement these performance critical techniques is again useful for the user, one simple and general feature is easier to reason about than many specialized features. Partial evaluation also allows us to increase performance by enabling zero-cost abstractions. An interpreter evaluating a statically known program of a DSL can be partially evaluated, leaving only code in the host language. Here partial evaluation is used like semantic macros are in other languages. The abstraction of the interpreter is removed.

Tasks:
- [ ] Core language
	- [ ] Language
		- [x] Dependent functions
		- [x] Dependent pairs
		- [x] Opt in laziness
		- [x] Uniqueness types
		- [ ] Evaluation time tracking
		- [ ] External interaction
			- [ ] `World`
			- [ ] Basic FFI 
	- [x] Typechecker
		- [x] Evaluator
		- [x] Unification
	- [ ] Partial evaluation
		- [ ] Termination checking
- [ ] Surface language
	- [x] Modules
		- [x] Definitions
		- [x] Imports
	- [ ] Typing
		- [ ] Dependent records
		- [ ] Uniqueness types
		- [ ] Evaluation time tracking
	- [ ] Pattern matching
	- [ ] External interaction
		- [ ] `World`
		- [ ] Basic FFI
- [ ] Backend
	- [ ] Backend IR
	- [ ] Codegen