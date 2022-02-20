Hmm, I wonder if having a logic language on the meta level gives you a sort of "extensible type system" (not sure if that's the right way to say it) on the object level. We add a type former
```
Γ ⊢ A : Type   Γ, x : A ⊢ B : Prop
———————————————————————————————————
       Γ ⊢ <x : A, B> : Type
```
Where `Type` is the universe of object level types and `Prop` the universe of meta level types. So really just a sigma type where the second component is erased. Anyway, we could define a proposition
```
Linear : [Γ ⊢ a → b] → Prop
```
Which demonstrates that a function is linear. We then have
```
LinearFunction : Π (a b : Type) → <f : a → b, Linear [. f]>
```
Then add some nice syntax
```
a ⊸ b = LinearFunction a b
```
And boom, linear types. I'm reasonably sure this sort of thing has been studied already, just need to find the literature. Possibly related topics:
1. Church vs Curry style typing
2. ATS's viewtypes
