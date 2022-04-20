![Peridot logo](./logo.png)

An experimental language for exploring the practical applications of two level type theory.

Discussion takes place on the [r/ProgrammingLanguages Discord server](https://discord.gg/jFZ8JyUNtn) - Projects K-P 🠒 #peridot.

### References and Inspiration

* [REFERENCES.md](./REFERENCES.md): A list of prior art that have influenced Peridot's design and implementation in major ways

### Information

* [RATIONALE.md](./notes/RATIONALE.md): An in-depth explanation of Peridot's design rationale
* [OLD_VS_NEW.md](./notes/OLD_VS_NEW.md): A comparison of Peridot and [Konna](https://github.com/eashanhatti/konna), a previous project of mine also based on 2LTT

### Introduction

Peridot is a functional/logic language based on 2LTT (two level type theory). It uses a logic language for the meta level, which allows for domain specific, declarative optimizers to be written entirely in userspace - writers of optimizers can focus on purely on the optimizations themselves. Meanwhile, the object language is high-level, dependently typed, and functional. Here's a very simple example of optimizing arithmetic:
```haskell
-- optimize `x * 2` to `x << 1`
optimize {~x * 2} {~y << 1} :- optimize x y.

-- optimize `x * y / y` to `x`
optimize {(~x * ~y) / ~y} {~z} :- optimize x z.

-- optimize both sides of a division
optimize {~x / ~y} {~z / ~w} :-
  optimize x z,
  optimize y w.

optimize {~x} {~x} :- int_literal x.

main =
    -- c = {3}, c = {(3 << 1) / 2}
    let optimize {(3 * 2) / 2} c
    -- 3
    in print ~(select smallest c)
```
