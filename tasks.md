### Small to medium sized tasks

2. Split `is_terms_eq` into `is_subtype` and `is_terms_eq`, where the first does what `is_terms_eq` does now and the second checks for structural equality
3. Record type decls currently do not retain their type parameters as indices, change that
4. Change `next_type` to allow for recursive types. Pass the clauses to it, have it compare the discrim with each and return `Whatever` if an irrefutable pattern matches with the new part of `discrim`
5. Change `next_type` to allow for matching on dependent types