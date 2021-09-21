### Two Level Type Theory Notes

The basics of 2LTT are present:
* `Type` is split into `Type0` and `Type1`. `Type0 : Type0` and `Type1 : Type1`
* "Same stage rule": Type formers stay at the same stage as the types they are applied to (all those types must be of the same stage), and eliminators must return a term of the same stage that was eliminated
* Lifting: Given `a : Type0`, we have `^a : Type1`, which is the type of code values in stage `s`. We then have quoting `~_ : a -> ^a` and splicing `!_ : ^a -> a`

Level 1 language:
* Full dependent types
* Inductive types
* Pure

Level 0 language:
* Simply typed
* Monomorphic
* Types are layouts
* Impure