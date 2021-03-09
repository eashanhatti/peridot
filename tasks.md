### Small to medium sized tasks

1. Fix the hack in `DoubElim` normalization. `DoubElim` has a special case where it normalizes to one branch if both branches are a `UnitTypeIntro`. Generalize this. Depends on *#2*
2. Split `is_terms_eq` into `is_subtype` and `is_terms_eq`, where the first does what `is_terms_eq` does now and the second checks for structural equality
3. Functions should store parameter names with a set that retains insertion order