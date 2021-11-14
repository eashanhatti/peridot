The regular old power function, which computes x^e.
```sml
fun pow (x:Nat) (e:Nat) -> Nat = case e of
  0 => 1
  _ => x * pow x (e - 1)
```
A staged power function. `Code a` is the type of code fragments that will compute a value of type `a` at runtime. The function takes `x`, a `Nat` code value, as well as `e`, a static (compile time only) `Nat`. The `1!` prefix indicates it is of stage `1` - known statically.
```sml
fun pow_staged (x: Code Nat) (e: 1!Nat) -> Code Nat = case e of
  0 => <1>
  _ => <~x * ~(pow_staged x (e - 1))>
```
Angle brackets `<_>` indicate the creation of a code value. The expression inside the angle brackets is "quoted".
The tilde `~_` indicates splicing - taking a code value and sticking it inside of another. For instance, after staging the following expression:
```sml
val x = <2 * 3>
val y = <~x + 3>
```
It becomes
```sml
val x = <2 * 3>
val y = <(2 * 3) + 3>
```

This `pow_staged` function is essentially a macro. Calls to it expand into a bunch of multiplications. E.g `pow <2> 3` becomes `2 * 2 * 2`. However, it has one flaw: We can't call it on exponents that aren't known fully at compile time:
```sml
val e = inputNat unit
val num = pow_staged <2> e
```
Typechecking this fails with the error ``Expected value of type `1!Nat`, got a value `e` of type `0!Nat`.``. `pow_staged` always expects a value of stage `1` (compile time) for the exponent, but we gave it a value of stage `0` - runtime.

What we need is a function that works across both stages - if the exponent is known statically, calls expand to a series of multiplications. Otherwise, it performs the computation fully at runtime, like the original `pow` did. Here is that very function, which uses stage polymorphism:
```sml
fun pow_staged_better (i:Stage) (j:Stage) (x: j!(Code i!Nat)) (e: j!Nat) -> j!(Code i!Nat) = case e of
  0 => <1>
  _ => <~x * ~(pow_staged_better x (e - 1))>
```
Here we see that the `!` is more general than just `0!` or `1!` - it takes an expression of type `Stage` on the left and a type on the right. There's also a new reduction rule for `Code`, `<_>`, and `~_` that allows this to work. Given one of those, if the term itself and the term inside it are of the same stage, it reduces to the term inside. For instance, `j!(Code i!Nat)` reduces to `i!Nat` when `j == i`. Let's look at the type of `pow_staged_better` at different combinations of levels:
```sml
pow_staged_better 0 0 : 0!Nat -> 0!Nat -> 0!Nat
(* And the function at these stages looks like: *)
fun pow_staged_better (x : 0!Nat) (e : 0!Nat) -> 0!Nat = case e of
  0 => 1
  _ => x * pow x (e - 1)
```
```sml
pow_staged_better 0 1 : 1!(Code 0!Nat) -> 1!Nat -> 1!(Code 0!Nat)
(* And the function at these stages looks like: *)
fun pow_staged_better (x: 1!(Code 0!Nat)) (e: 1!Nat) -> 1!(Code 0!Nat) = case e of
  0 => <1>
  _ => <~x * ~(pow_staged_better x (e - 1))>
```
```sml
pow_staged_better 1 1 : 1!Nat -> 1!Nat -> 1!Nat
(* And the function at these stages looks like: *)
fun pow_staged_better (x : 1!Nat) (e : 1!Nat) -> 1!Nat = case e of
  0 => 1
  _ => x * pow x (e - 1)
```
Note that `pow_staged_better 0 1` results in a function identical to `pow_staged`. Additionally, `pow_staged_better 0 0` and `pow_staged_better 1 1` result in a function identical to the original `pow`, just at different staged. `pow_staged_better` subsumes both of the earlier functions. We now have a very flexible function - it can be either fully evaluated at runtime, fully evaluated at compile time, or specialized to the exponent (partially evaluated).