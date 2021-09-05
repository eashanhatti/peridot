## Staging

#### Overview

A term's stage determines when its concrete value can be known. Evaluation is performed at a certain stage. Given a term of stage `s` and evaluation performed at `s'`, if `s /= s'`, the term will not be evaluated. In the same case, eliminating a staged term will not reveal the term's value to the body of the eliminator.

There are three stages: `0`, `1`, and `2`. Typechecking is performed at stage `2`, partial evaluation at stages `1` and `2`, and runtime at stage `0`. The distinct partial evaluation stage is needed for when one wants a definition to remain abstract to the typechecker, but also wants it to be partially evaluated. Such a definition would be of stage `1`.

#### Thoughts

Should the `0` stage be exposed to the user? As far as I've thought, it's only needed for expressing foreign functions and allowing for separate compilation. Explicit stage annotations aren't needed for the former. For the latter, it might be better if it were a compiler switch rather than an annotation on definitions - that would make it easier to switch between separate compilation and whole program compilation for debug vs release.