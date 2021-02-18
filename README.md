# Clamn
Clamn is intended to be a functional systems language. What I want it to be is a language that enables the abstractions used in functional programming while providing the performance and performance *guarantees* of systems languages. Idiomatic functional code should be able to be written without sacrificing performance.

Most functional languages are not known for their performance. A major reason for this is the high amount of abstraction used in functional code. This abstraction can come in many flavors, but two of the most important ones are higher order functions and polymorphism. These problems *can* be fixed with an optimizing compiler. However, this is not an ideal solution for a systems language. Optimization is compiler-driven and thus can be unpredictable, requiring the programmer to have a more complex mental model of the program. The programmer has to keep in mind not only what the program does, but also how to write it in such a way that the compiler will optimize it the best. In any systems language, performance should be programmer-driven, which means that it needs to be visible and controllable in the semantics of the language.

To that end, the main two features I want to implement in Clamn are a staging system and dependent types. The essence of staging is that it allows one to specify *when* a computation takes place, which makes it a method for controlled partial evaluation. Partial evaluation even on its own is very useful. It allows us to easily eliminate the overhead of higher order functions. In addition, it can be used to eliminate the overhead of interpreted DSLs by partially evaluating the DSL's interpreter on a statically known program. Partial evaluation can however, be even more useful when combined with dependent types. Under dependent types, polymorphism can be expressed as a computation, meaning that partial evaluation can be applied to it. Partial evaluation can then be used to express monomorphization, allowing the overhead of polymorphism to be removed in most places. Staging combined with dependent types allows the overhead of the abstractions used in functional languages to be removed in a programmer-driven way.

There are a few features I want to implement, but are less of a priority, namely (in no particular order):
* **Algebraic Effects**. They seem like a good alternative to monads for effects, their ergonomics look nice.
* **Levity Polymorphism**. Staging combined with dependent types does allow for some control over memory layout if types are treated as representations, but I'd like for it to be more fine-grained
* **Multiple Memory Management Options**. I probably won't go with tracing GC, multiple memory management options are very nice to have in a systems language

Current work is in increasing the elaborator's performance and implementing dependent records. Staging and pattern matching are next on the list of things to implement.\
Current Roadmap:
- [ ] Core language
	- [ ] Language
		- [x] Dependent functions
		- [x] Dependent pairs
		- [x] Opt-in lazy eval
		- [x] Uniqueness types
		- [ ] Staging
		- [ ] Levity Polymorphism
		- [ ] External interaction/effects
			- [ ] `World`
			- [ ] Basic FFI 
	- [x] Typechecker
		- [x] Evaluator
		- [x] Unification
	- [ ] Partial evaluation
		- [ ] Totality checking
- [ ] Surface language
    - [ ] Elaborator
	- [x] Modules
		- [x] Definitions
		- [x] Imports
	- [ ] Typing
		- [x] Dependent functions
		- [ ] Dependent records
		- [ ] Staging
		- [ ] Levity Polymorphism
		- [ ] Basic type inference
	- [ ] Pattern matching
	- [ ] External interaction/effects
		- [ ] `World`
		- [ ] Basic FFI
- [ ] Backend
	- [ ] Simple codegen