# Clamn

Clamn is intended to be a functional systems language. My motivation behind the project is the desire to have a functional language that provides the performance and performance *guarantees* of systems languages like Rust, C++, and D. Idiomatic functional code should be able to be written without sacrificing performance.

Major Desired Features:
* **Dependent Types**. Dependent types are often talked about in the context of theorem proving, but they're very useful for general programming as well. Many common and often essential language features use a subset of dependent types, e.g generics, const generics, and safe tagged unions. Implementing dependent types themselves give you those features for free and more. Dependent types can however, have performance and ergonomics issues. I'd like to improve that here.
* **A Staging System**. The essence of staging is that it allows you to express *when* a computation takes place. This is useful in general for performance, you can track what computations are known at compile time. However, it becomes even more useful in functional languages with dependent types because both functions and types are first-class, meaning they can be staged. Because of this, staging allows you to express essential optimizations like inlining, monomorphization, specialization, etc. Inlining becomes the staging of a function, monomorphization becomes the staging of a function that takes a staged type, etc. Staging makes these big optimizations controllable, they become performance guarantees.
* **Control Over Memory Layout**. Most functional languages have to use a uniform representation, which can severly impact performance. That impact can be alleviated with optimization, but it needs to be a guarantee in a systems language. Levity polymorphism used together with staging is one way to do this.
* **Multiple Memory Management Options**. Most functional languages use tracing GC, but that method isn't always the best for performance. Multiple memory management options are always needed in a systems language.
* **Effect Tracking**. Many of the fancier type system features that I want to leverage (such as dependent types) break in the presence of unconstrained effects. Effect tracking is needed because of that. Algebraic effects seem like the most likely route I will go.

Current Roadmap:
- [ ] Core language
	- [ ] Language
		- [x] Dependent functions
		- [x] Dependent pairs
		- [x] Opt in laziness
		- [x] Uniqueness types
		- [ ] Staging
		- [ ] Representation tracking
		- [ ] External interaction/effects
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
		- [x] Dependent functions
		- [ ] Dependent records
		- [ ] Staging
		- [ ] Size tracking
	- [ ] Pattern matching
	- [ ] External interaction/effects
		- [ ] `World`
		- [ ] Basic FFI
- [ ] Backend
	- [ ] Backend IR
	- [ ] Codegen