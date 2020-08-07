# lang3

- low level functional language
- think this: you could implement a garbage collector in it
- allows to deal with pointers
- referential transparency
- control over inlining
- control over boxing
- zero cost abstractions

adding a new feature to the type system is fine as long as it does not depend on any other features
whenever a feature subsumes two or more features, that feature should be added and the multiple removed

## 1 uniqueness types

a uniqueness type is a type `T p` where `p = Unique`, in contrast to `T : Shared`\
for any value `x` and type `T Unique`, `x` may be used only once\
for any function type `{A} -> B` where a unique type occurs in `A` and `B`, in place mutation will be used, since referential transparency can be maintained\
example:
```
plusOne : (Int Unique) -> (Int Unique)
plusOne x = x + 1
```
a pointer to `x` will be mutated to contain `x + 1`, instead of returning a new `Int`\
using this, stack variables can also be used\
for any function `f` which contains no unique types in its input *or* output that calls a function which *does* contain a unique type in its input or output
`f` will be compiled to a function with a stack variable\
a contrived example:
```
plusOne : (Int Unique) -> (Int Unique)
plusOne x = x + 1

f : Int -> Int
f x = plusOne (uniqueFrom var)
```
would be compiled to:
```
Unit plusOne(Int* x) {
    *x = *x + 1
}

Int f(Int x) {
    Int var0 = uniqueFrom(x)
    plusOne(&var0)
    return var0
}
```
there was something new there: `uniqueFrom`. it is not a keyword or a builtin, it is part of the next topic in uniqueness types

---

uniqueFrom takes a nonunique value and returns a unique value\
for reference type, you could imagine that it performs a deep copy, for value types a normal copy, etc\
in the language, it could be part of an interface:
```
interface NonuniqueToUnique A where -- long name, but whatever, it's a placeholder
    uniqueFrom :: A -> unique A -- for now, imagine unique is a function which converts a type in NormalType to a type in UniqueType, however, this should be further examined
```
you could imagine another interface like `Clone` from rust:
```
interface Clone A where
    clone :: unique A -> unique (unique A, A)
```

another thing, for any parameterized type `T`, if a parameter of `T` is unique, `T` must also be unique

note: for now unique values can be implicitly converted to unrestricted values, should later put this in userspace and make the implicit conversion syntactic sugar instead

## 2 function types

pi types take the form `{x : A} -> B` where `x` may occur in `B` (`vs` is elaborated upon in **2.1**)

### 2.1 free variables

the `vs` in the function type is the set of the free variables in a function\
this way, the amount of space needed for a closure can be known at compile time, so they can be stack allocated\
take `add` as an example (assume the primitive `+`) (the angle bracket syntax denotes free variables):
```
add : <> Int -> <Int> Int -> Int
add = lam x . lam y . x + y
```
there is also a subtyping relationship between pi types where one pi type's set of freevars is a subset of the other pi type's set of freevars
for example, `<> Int -> Int :< <Int> Int -> Int`

## 3 staged data

stages allow expressing in the type system *when* ceratin data can be used\
all types are indexed by their stage\
for any two terms `x` and `y`, where `x` is of stage `n` and `y` is of stage `m` and `y` is a subterm of `x`, such is valid if `n in m`\
for now, valid stages are limited to the intervals `0..0`(or just `0`), `1..1`(or just `1`), and `0..1`\
in the examples, the default stage is `0..1`

there are many desired features that emerge from staging, this one simple feature, all of those will be covered here

here is an example of using stages to encode the notion of external functions; functions which can only be called at run time (forget effects for the moment):
```
alloc : (A : Type -> Ptr A) 0 -- alloc is an extern function, say, declared in a C lib to be linked to

main : (Ptr Int) 0
main = alloc Int -- typechecks, main is declared to exist at stage 0

bad_main : (Ptr Int) 1
bad_main = alloc Int -- does not typecheck, bad_main is declared exist stage 1 while alloc exists at stage 0

bad_main' : (Ptr Int) 0..1
bad_main' = alloc Int -- also does not typecheck, bad_main' is declared to be able to exist at stage 0 or 1, while alloc can exist only at stage 0
```

here is an example of a `map` function which is gauranteed by the type system to be monomorphized, and yields a type error if such is not possible:
```
map : (A B : Type 1) -> (A -> B) -> List A -> List B
map _ _ f list =
	let
		map_inner : (A -> B) -> List A -> List B
		map_inner f (Cons x xs) = Cons (f x) (map_inner f xs)
		map_inner _ [] = []
	in map_inner f list
```

the type parameters `A` and `B` are declared to be of type `Type 1`, the stage `1` indicating that they only exist at compile time\
now, why is map inner needed? such will be explained:
```
map : (A B : Type 1) -> (A -> B) -> List A -> List B
map A B f (Cons x xs) = Cons (f x) (map A B f xs)
map _ _ _ [] = []
```
this version of map, the version seen in most languages, fails with a type error, which would look something like this:
```
Error: stage 1 function 'map' called in stage 0 function (anonymous function returned by 'map')
```
the error is saying that `map` can only be called at compile time, the issue is that the function `map` returns, which is of type `(A -> B) -> List A -> List B`, is of stage `0..1`, the function we are recursively calling `map` inside\
a way to think of this is that we are trying to tell the compiler to monomorphize `map` *at run time*, which doesn't make any sense. that is why we need `map_inner`\
it does indeed make it more difficult to write `map` with this system, luckily the difficulty could be removed with syntax sugar or something else along that line

## 4 compiler design

```
frontend language
|
| lowered to core language
v
core language
| raised to frontend language for error
|---------------> frontend language
v
backend language
```