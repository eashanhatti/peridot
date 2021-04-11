### Small to medium sized tasks

2. Split `is_terms_eq` into `is_subtype` and `is_terms_eq`, where the first does what `is_terms_eq` does now and the second checks for structural equality
3. Record type decls currently do not retain their type parameters as indices, change that