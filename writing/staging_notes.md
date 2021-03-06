## Staging

Kinds are indexed by their stage: `Type s`\
`sta'T` and `dyn'T` will be syntactic sugar for `T : Type static` and `T : Type dynamic`. Or more generally, `s'T` is `T : Type s`

Stage polymorphism is by default implicit, hence
```haskell
id : (T : Type) -> T -> T
id T x = x
```
elaborates to
```haskell
id : sta'(s1, s2, s3 : sta'Stage) -> s1'(T : s2'Type) -> s3'(T -> T)
id T x = x
```
This `id` will be monomorphized if we explicitly stage the `(T : Type) -> ..`
```haskell
id : sta'(T : sta'Type) -> T -> T
id T x = x
```
`id` takes a `Type` that is evaluated at compile-time. `id` itself is also evaluated at compile-time, and returns a monomorphic function that can be used at any stage. Here, staging expresses monomorphization

Staging can also express inlining
```haskell
double_then_add : sta'(x : Int) -> sta'(y : Int) -> Int
double_then_add x y = x * 2 + y
```
The `double_then_add` function itself will be fully evaluated, however, its body and argument will not
```haskell
double_then_add 3 4
```
Looks like this at run-time:
```
3 * 2 + 4
```

Let's now extend this system with control over data representation. We'll add another index to `Type` of type `Rep`. `Type s` is now `Type s r`\
`s'r'T` is now sugar for `T : Type s r`\
Representation polymorphism is implicit by default
```haskell
id : sta'(rep : sta'Rep) -> sta'(T : s1'rep'Type) -> T -> T
```
Note that this example isn't much different than the above `id` without representation polymorphism, since in that example the type `T` itself acted as the representation. However, decoupling types from representations does yield more control, useful for more complex cases\
There's a problem with this system though, we can do things like this (side-by-side comparison with the above `id`):
```haskell
id : sta'(rep : sta'Rep) -> sta'(T : s1'rep'Type) -> T -> T

id : sta'(rep : dyn'Rep) -> sta'(T : s1'rep'Type) -> T -> T
```
We changed the `sta'Rep` to a `dyn'Rep`, meaning that `rep` will now only be known at run-time. This is a problem, how do we compile `id` now? We could compile functions with an argument of unknown representation to a function taking a pointer, but that somewhat defeats the purpose of representation polymorphism in the first place. What we want is for the type system to tell us that this cannot be compiled straightforwardly

To that end, we can extend this system yet again with erasure. We'll add another index to `Type` of type `Erased`. `Type s r` is now `Type s r i`. For `A : Type s _ true`, `A` can only appear in types that are also erased and of the same stage. For instance. where `A : Type static _ true`, `(A -> A) : Type dynamic _ _` is invalid. Note that erasure is somewhat of a bad name here, as it does not mean that a term must specifically be entirely static, rather, it just has to be entirely of one stage\
`s'r'i'T` is now sugar for `T : Type s r i`

We do not require that all `Reps` be erased and static, rather, we have the *arrow* require this of only its input and output types. This way we can still have values of a dynamically known representation, which is sometimes necessary
```haskell
-------
Rep : Type s r i
```
```haskell
rA : Rep : Type static reprep true
rB : Rep : Type static reprep true
A : Type sA rA iA
B : Type sB rB iB
----------------------------------
(A -> B) : Type sF funrep iF
```
Let's try to write the `id` with a `rep : dyn'Rep` argument
```haskell
id : sta'(rep : dyn'Rep) -> sta'(T : s'rep'Type) -> T -> T
```
This does not typecheck, `rep` must be `static` because it is used as the representation of `T`, the parameter of a function. We'll cut out the less relevant bits
```haskell
id : sta'(rep : sta'Rep) -> ..
```
This also does not typecheck, `rep` must be erased, again because it is used as the representation of `T`
```haskell
id : sta'(rep : sta'_'true'Rep) -> ..
```
This typechecks. Additionally, because of erasure, we cannot cheat and try to have the function taking `rep` be `dynamic`
```haskell
id : dyn'(rep : sta'_'true'Rep) -> ..
```
This does not work, because `rep` is erased, it may not be contained in data of different stages

Problem: Polymorphism is now impossible in some cases. Because erasure imposes restrictions on the forms types can take, we must assume the highest restriction when it isn't known. In this case, that means we must always assume a term's erasure is `true` if the erasure is not a concrete value
```haskell
data List : (A : s1'r'i1'Type) -> s2'_'i2'Type where
    nil : List A
    cons : A -> List A -> List A
```
This doesn't actually work, `i1` and `i2` are assumed to be true, making it error on the fact that `s1` does not equal `s2`
```haskell
decide : Erased -> Stage -> Stage -> Stage
decide i s1 s2 =
    case i of
        true => s1
        false => s2

data List : (A : (decide i s1 s2)'r'i'Type) -> (decide i s1 s3)'_'i'Type where
    nil : List A
    cons : A -> List A -> List A
```
Thought this would work at first, but it actually doesn't. `(decide i s1 s2)` does not equal `(decide i s1 s3)`. I think this is the same issue Coq has with `Prop` vs `Type`

And so, we end up needing different types for erased terms vs non-erased terms
```haskell
data ListOfErased : (A : s'r'true'Type) -> s'_'true'Type where
    nil : List A
    cons : A -> List A -> List A

data ListOfNonErased : (A : s1'r'false'Type) -> s2'_'false'Type where
    nil : List A
    cons : A -> List A -> List A
```

Thinking about it again, this actually shouldn't be a problem. Let's take the one using `decide` again
```haskell
decide : Erased -> Stage -> Stage -> Stage
decide i s1 s2 =
    case i of
        true => s1
        false => s2

data List : (A : (decide i s1 s2)'r'i'Type) -> (decide i s1 s3)'_'i'Type where
    nil : List A
    cons : A -> List A -> List A
```
It seemed like this would fail because `(decide i s1 s2) /= (decide i s1 s3)`. However, the fact that it has to assume `i` will be `true` here will cause them both to normalize to `s1`, making the well-formedness check pass. Note that that assumption only occurs during the well-formedness check, otherwise that would cause some weird behavior

I'll need to make sure rigorously that this system is correct, but it looks like it will work