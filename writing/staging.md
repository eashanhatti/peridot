# Clamn

This is an idea of what I would want the language to look like for it to be considered useful

Main features:
* Staging
* Dependent types
* Levity polymorphism

Clamn is meant to be a *functional systems language*, the above features are meant to allow for high and predictable performance

## Staging

Staging is extremely useful in a dependently typed language. To understand why, take the identity function in Rust:
```rust
fn id<T>(x: T) -> T {
	return x;
}
```
Now let's implement the same function Idris, a dependently typed language:
```idris
id : (T : Type) -> T -> T
id T x = x
```
They may seem equivalent. There is however, a difference between the two. That is, the Idris `id` function lacks a *phase distinction*. In Rust types and values are completely different things, and because of this it can separate them onto different *phases*. Types exist at compile time while values exist at runtime. Because types exist only at compile time, polymorphism has no overhead. Rust can always monomorphize the types away. Idris however, lacks this. Because Idris is dependently typed, there is no distinction between types and values, and thus, no *phase distinction*. Types and values can both exist at runtime and compile time. Because of this, Idris is not guaranteed to be able to erase types and remove the overhead of polymorphism (it will have to box the `x` argument). Despite that, dependent types provide a huge amount of expressiveness. We would like to keep them while also getting the performance guarantees of Rust's generics.

*Staging* allows us to do exactly that. The essence of staging is that it allows you to state *when* a computation takes place, allowing us to reintroduce phase distinctions wherever we want. Let's imagine a version of Idris with staging and write the actual equivalent to Rust's `id`.\
**Note**: 'stage' and 'phase' mean the same thing
```idris
id : Static (T : Type) -> T -> T
id T x = x
```
Here, the function from `T : Type` to `T -> T` is of stage `Static`, meaning that it will execute at compile time. Note that we did not write this:
```idris
id : (T : Static Type) -> T -> T
id T x = x
```
This means something different. After compile time evaluation, this is what calling each of the two will look like\
The first:
```idris
id (if true then Int else String) 34
-- this becomes
(\x : Int => x) 34
```
The second
```idris
id (if true then Int else String) 34
-- this becomes
id Int 34
```
The first fully evaluates the function from `T : Type` to `T -> T` at compile time, resulting in a monomorphized version of `id`. The second fully evaluates the `T : Type` at compile time, but *does not* evaluate the function taking it.