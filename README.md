# Konna

An experimental language for exploring the practical applications of two level type theory.

### Introduction

A common pattern in languages with performance as a goal is to have some features be compile time only ("static"). C++ templates for instance, eliminate the overhead of polymorphism by statically generating specialized versions of each templated definition. However, another common trend is for these compile time languages - at the start very simple - to accrue more and more features that interact in ad hoc ways, harming ergonomics.

The problem here is not with the idea itself, but rather the execution. These static languages aren't designed from the start to be *actual languages*. Konna has a static language and a runtime language, but the static language is fully featured from the start. The static language is dependently typed, pure, and can manipulate programs of the runtime language as data. In contrast, the runtime language is monomorphic and impure. The combination of these two allows features such as conditional compilation, templates, user-directed inlining, compile time evaluation, macros, and specialization of DSLs to be expressed very naturally.

The language is a WIP, so there's numerous nontrivial bugs. However, currently the only barrier to writing "real" programs in it is the lack of IO.

### References and Inspirations

Prior art on two level type theory.

**Two-Level Type Theory and Applications**
> We define and develop two-level type theory (2LTT), a version of Martin-Löf type theory which combines two different type theories.\
https://arxiv.org/abs/1705.03307

**Staged**
> Experimental staged language with dependent types\
https://github.com/AndrasKovacs/staged

Elaboration of dependent pattern matching.

**Elaborating dependent (co)pattern matching**
> We present an algorithm elaborating definitions by dependent copattern matching to a core language with inductive datatypes, coinductive record types, an identity type, and constants defined by well-typed case trees.\
https://dl.acm.org/doi/10.1145/3236770

Projects exploring a similar design space.

**Basil**
> Lisp dialect featuring highly flexible syntax, arbitrary compile-time evaluation, and static types!\
https://github.com/basilTeam/basil

**Spiral**
> Functional language with intensional polymorphism and first-class staging.\
https://github.com/mrakgr/The-Spiral-Language

Structured editing.

**Sapling**
> A highly experimental code editor where you edit code, not text.\
https://github.com/kneasle/sapling

**Alfa**
> Alfa is a successor of the proof editor ALF, i.e., an editor for direct manipulation of proof objects in a logical framework based on Per Martin-Löf's Type Theory.\
https://cth.altocumulus.org/~hallgren/Alfa/

**Hazel**
> Hazel is a live functional programming environment that is able to typecheck, manipulate, and even run incomplete programs, i.e. programs with holes.\
https://hazel.org/

### Examples

The type of runtime-relevant pairs. Product types are tuples, not records - fields are not named.
```
product Pair : (a:U0) -> (b:U0) -> U0
    a
    b
```
Erased natural numbers and the unit type.
```
datatype Nat : U1
    zero : Nat
    succ : Nat -> Nat

product Unit : U0
```
An array type, implemented as nested pairs.
```
val Array : Nat -> U0 -> U0 = case
    zero _ => Unit
    (succ n) a => Pair a (Array n a)
```
A `map` function for arrays. `<_>` indicated quoting, `~_` indicates splicing, and `Code _` is the type of a quoted code fragment. `#T` indicates the construction of or pattern matching on a product value.
```
val map : (n : Nat) -> (a : U0) -> (b : U0) -> Code ((a -> b) -> Array n a -> Array n b) =
    λn a b => case n
        zero => <λf arr => case arr
            #Unit => #Unit>
        succ n => <λf arr => case arr
            #Pair x arr => #Pair (f x) (~(map n a b) f arr)>
```
Implicit arguments, function definition syntax, and implicit splicing/quoting have not been implemented, hence why this example is rather cluttered. Here's what it would look like with those features:
```
fun map (n : Nat) (a b : U0) = case n
    zero => λf #Unit => #Unit
    succ n => λf (#Pair x arr) => #Pair (f x) (map n a b f arr)
```
More pattern matching.
```
val max : Nat -> Nat -> Nat = case
    zero m => m
    n zero => n
    (succ n) (succ m) => succ (max n m)
```
Dependent pattern matching.
```
datatype Bool : U1
    true : Bool
    false : Bool

datatype IsTrue : Bool -> U1
    is_true : IsTrue true

val foo : (b : Bool) -> IsTrue b -> ? = case b of
    true is_true => ?

(* Fails to typecheck. Error messages are pretty ugly at the moment, but the core
   of the error says "Expected pattern of type `IsTrue false` in second pattern
   of `case` expression, but pattern `is_true` is of type `IsTrue true" *)
val bar : (b : Bool) -> IsTrue b -> ? = case b of
    false is_true => ?
```

### Planned Features

* IO
* Compilation to native code
* Extensible datatypes
* Arity polymorphism for higher order functions
* Linear/uniqueness types
* Stage polymorphism