# lang

low level function language\
if anybody's ever looking at this, this is just for me to get my ideas down on paper, don't take it too seriously

## uniqueness types

uniqueness types allow to mark values that should only be used once\
for any variable `x` which may be used in `e`, where `x : T : UniqueType`, `x` may only be used once\
if the kind of the variable is unknown, it is assumed to be `UniqueType`

unique types are also *infectious*, for any type `A` which contains a type `B : UniqueType`, `A` must also be of `UniqueType`, the exception to this are pi types, the pi type is only required to be unique if it captures a unique variable, for instance, `(A -[V : UniqueType]> B) : UniqueType` is well typed, `(A -[V : UniqueType]> B) : SharedType`

unique types also allow for mutation while retaining referential transparency, if a type `A : UniqueType` appears in both the input and output types of a pi type, the function is compiled to use mutation\
`TODO: examples`

## partial evaluation

partial evaluation is a major feature of lang, as it allows to encode optimizations such as inlining, monomorphization, and constant folding\
partial evaluation's presence in the type system also allows for the encoding of staging

## syntax extensions

## type sizes

## macros