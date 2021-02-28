### Small to medium sized tasks

1. Fix the hack in `DoubElim` normalization. `DoubElim` has a special case where it normalizes to one branch if both branches are a `UnitTypeIntro`. Generalize this. Depends on *#2*
2. Split `is_terms_eq` into `is_subtype` and `is_terms_eq`, where the first does what `is_terms_eq` does now and the second checks for structural equality
3. Bring core term construction macros out of `surface_to_core` and into their own file
4. Remove universe levels from the core language
5. Reduce bloat for `discrim_type` in module elaboration
6. Sort out the weird situation with `synth_type` vs `r#type`. `synth_type` should subsume `r#type`, but `r#type` is also useful because it doesn't check the type returned. Maybe give `r#type` the functionality of `synth_type` but without the checking. Then have `synth_type`'s implementation use `r#type`, but it also checks what `r#type` returns