### Braindump

This is a stream of conciousness. Definitely no guarantee about it making sense.

#### No date

What to do about currying? Explicit currying would be preferred over implicit. E.g where `foo : a -> b -> c`, `foo x _` instead of `foo x`. That also makes choosing the right order of arguments when defining a function less important. The error messages when you forget an argument are also not very nice. Problem is this requires multiarg functions, which are less nice theory-wise.

Maybe I can have multiarg functions in the surface language and elaborate them to single-arg functions?

First class argument lists?
```sml
fun apply [im a : Type, im pl : Params, f : pl -> a | ps : pl] =
  f @ ps

fun add [x, y] = x + y

apply (add _ _) 3 4
```

#### 9/15/2021

Row polymorphism?
```haskell
data Row
  = Ordered Label Type Row
  | Unordered (Map Label Type) Row
  | Var RowVar
  | End
```
(Something like this representation) `Ordered` is for dependent types. Does that work? Or does it break things? I don't think I've ever seen row polymorphism in a dependently typed language, so I'm not sure.

Anyway:
```haskell
data Term =
  Pi Row Term
  ...
```
We lose the varargs-like thing that was demonstrated above with `apply`. Can that be recovered?

Huh, wait, hold that thought. How do implicit arguments factor into this? Let's say we have row polymorphic records? If we mark "implicitness" on the row, can we have *implicit fields*?

Anyway, ad-hoc varargs thing:
```sml
fun apply [im a : Type, im pl : Row, f : pl -> a | pl]
  f @ varargs
```
Where varargs only works in a function with a `|` extension? Not sure haha.

That implicit fields thing is interesting. Hmm, how does that work for extensible variants? They would use rows.

I think it *doesn't* work.
```haskell
data Row
  = Ordered Label Type Row
  | Unordered (Map Label Type) Row
  | Var RowVar
  | End

data PassingMethod = Implicit | Explicit

data Term =
  Pi Row (Map Label PassingMethod) Term
  ...
```

Huh, how do `Unordered` arguments work? Would they have to be passed as named parameters? That seems like the most reasonable thing to do. For records it makes sense as well - some fields have to be passed in order

Gah, what does `Ordered` mean for variants?

Maybe we have to separate `Row` into dependent and non-dependent versions

#### 9/16/2021

Meh, row polymorphism doesn't seem like it'll work for function types. Really, I just want n-ary functions for the better error messages and explicit currying. I probably don't need something as big as what I've been mulling over above if those are all I want.

I'd like to avoid any additions to the core language, if at all possible..

Yeah I'm just going to set this aside for now

#### 9/17/2021

From https://www.youtube.com/watch?v=OmNqXP9Hp_A

2LTT:
```haskell
Type 0 : Type 0
Type 1 : Type 1
```

All type formers/eliminators stay on the same stage, for instance
```haskell
Γ ⊢ A : Type i   Γ, x : A ⊢ B : Type i
---------------------------------------
       Γ ⊢ (x : A) → B : Type i
```

Lifting operation: Given `A : Type 0`, `^A : Type 1`

Given `e : A`, `<e> : ^A`\
Given `e : ^A`, `[e] : A`
```
<[e1]> = e1
[<e2>] = e2
```

So programs at stage `1` are CTE'd. Ooh, you could extend this with pattern matching for `^A` values - code values. Stage polymorphism would be another cool addition. Stages would be restricted to stage `1`.

This actually looking a lot like what I was thinking about in https://github.com/eashanhatti/konna/issues/2/. The problem I ran into was that functions of stage `0` couldn't be contained in data of stage `1`. This was because I didn't have the "All type formers/eliminators stay on the same stage" rule. I attempted to solve it with an additional stage `2`, which is stage `1` in 2LTT + the same stage rule and then bar functions from being on stage `1`, but that necessitated a complex constraint system. Dang, I wish I had checked out 2LTT earlier! This fixes the problems with the system I had come up with.

https://www.youtube.com/watch?v=ove4TQsXemY
Hm, since we can define lowering functions from `1` to `0`, is stage polymorphism needed?

> Stages would be restricted to stage `1`.

Huh, no this actually wouldn't work because any stage polymorphic function would then have to be at stage `1`.. which means it isn't stage polymorphic. So lowering instead of stage poly might be better. I hope lowering functions can be derived. If they can't then I'll have to go with stage poly - however it should work.

#### 9/18/2021

From https://www.youtube.com/watch?v=WOd0ZFbJfQg

Random notes:
* The runtime language can have unrestricted side effects, since typechecking will only perform stage 1 computations
* The comptime language can be dependently typed and higher order, while the runtime language can be simply typed, monomorphic, and first order.
* Partially static data. Elements of `List A` are code values, while the list structure itself is static
```haskell
data List (A : ^U0) : U1 where
  nil : List A
  cons : ^[A] -> List A -> List A
```

From https://www.youtube.com/watch?v=ai4vU1Naopk

Notes: Programming without closures. On stage 0:
* Restrict stage 0 functions be strictly positive: Split a universe V0 off from U0. V0 is a subuniverse of U0 and is closed under inductive types but no function types. Eliminations must also stay in the same universe (Can you lift out `case` expressions during elaboration to make this less restrictive?). The function type in U0 then becomes
```haskell
Γ ⊢ A : V0   Γ ⊢ B : U0
------------------------
    Γ ⊢ A → B : U0
```
```haskell
map : {a b : ^U0} -> (^[a] -> ^[b]) -> ^(List [a]) -> ^(List [b])
```
* Regular dependent type theory on stage 1

Hm, is not being able to store closures in inductives too big of a restriction? (Maybe that'll be answered later in the video)

Ack, yeah seems you need to defunctionalize by hand if closure + inductive comes up. Maybe that's not too bad. Huh actually, I wonder if you could have a higher order function type where defunctionalization is guaranteed. It would inhabit U0. If I understand correctly, code size blowup can occur when defunctionalizing, so it may be worth it to also have a regular higher order function type in U0 as well, which simply takes regular closures. Can we have a subtyping relationship between these three as well? Note that the stage 0 language remains monomorphic.

Let's try without that stuff for the first implementation.

Should there be an arbitrary number of stages or just U0/U1?

#### 9/20/2021

No, we can just have U0/U1

#### 9/26/2021

Hm, is monomorphization really guaranteed in all cases?
```haskell
assume ty : Unit -> U0

id : (a : ^U0) -> ^[a] -> ^[a]
id _ x = x

_ = id <ty unit> <undefined>
```
Post-staging this is
```haskell
assume ty : Unit -> U0

_ = <undefined> : ^(ty unit)
```
So no, it isn't. `ty unit` sticks around at runtime

Aha, I just need to disallow first-class types in the object language.

#### 10/20/2021

Note: `a ~> b` is the type of dynamic functions, `a -> b` is the type of static functions

How does tail recursion fit into the current system? My first idea was to have a separate function type that guarantees TCO, but how does that work with inlining? Inlined functions take the form `^a -> ^b` - they're static functions. We could add another metafunction type that also guarantees TCO? Not sure what the semantics of that would be.

Hm. What if "`^a -> ^b` is the type of inlined functions" is the wrong way of thinking about things?

What if we put how much stack space a function's recursive calls will consume on its type? So we have two values, `bounded` and `unbounded`. Nonrecursive and tail recursive functions are of type `a ~bounded> b`, and everything else are of type `a ~unbounded> b` (Temporary syntax). The former can be inlined and TCOd. So "`^a -> ^b` is the type of inlined functions", *is* the wrong way of thinking, although it is accurate in a sense. It's more accurate however, to say that `^a -> ^b` is the type of a macro.