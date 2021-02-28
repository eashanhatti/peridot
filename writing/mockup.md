# Mockup

Clamn is intended to be a functional systems language. This is roughly what the language will look like when it's in a more finished state:

#### Functions 
Here is an identity function, square brackets enclose parameters that are evaluated at compile time. Since `T` is known at compile time, `id` will be monomorphized.\
Ignore the `(r)` in `Type(r)` for now.
```ml
fun id[T : Type(r)](x : T) -> T = x
```
It could also be written as
```ml
val id : [T : Type(r)] -> T -> T
let id = fun T, x => x
```
Or
```ml
let id : [T : Type(r)] -> T -> T = fun T, x => x
```
Calling `id`
```ml
id(Int, 3)
id(String, "foo")
```

If multiple parameters have the same type, you can group them together and only write the type once.
```ml
fun const[T : Type(r)](x, y : T) -> T = x
```

#### Implicit parameters

```ml
val id : T -> T
let id = fun x => x
```
Here is a version of `id` that uses implicit parameters. If a name is used in a type signature without declaring it, the compiler will add a parameter marked as `implicit` to the type. A parameter marked as `implicit` will have its value inferred at call sites. This is the explicit version of `id`:
```ml
val id : [implicit T : Type(r)] -> T -> T
let id = fun T, x => x
```
Implicit parameters are by default made compile time (hence the square brackets).
Note that this actually still has an implicit parameter: `r`, which is passed to `Type`. That will be covered later.

As said, the compiler will infer the value of `T` at call sites:
```ml
id(3) // no need to explicitly pass `Int`
```
But `T` can be passed explicitly if needed (the syntax will probably be changed):
```ml
id(implicit Int, 3)
```

#### Structs

A `struct`:
```ml
struct Foo : Type(r) where
    bar : Int
    baz : String
    bat : Float
end
```
In the first line, we declare the `struct`'s name, and then its type\
`struct`s can have parameters, in which case it will have a more complex type.
```ml
struct Foo : (T : Type(r1)) -> Type(r2) where
    bar : T
end
```

The generic `Foo` could be used like this
```ml
let foo : Foo(Int) = Foo { bar = 23 }
let foo2 : Foo(String) = Foo { bar = "baz" }
```

`struct`s support dot access for fields
```ml
struct Point : Type(r) where
    x : Int
    y : Int
end

let point = Point { x = 3, y = 6 }
let point_x = point.x // dot access
```

#### Layout polymorphism

Here we have `Either`, a tagged union. The data is stored flat and unboxed. Now the `(r)` in `Type(r)` seen earlier comes in. With layout polymorphism, types carry some extra information: their in-memory representation. That information is carried as a parameter on the type of types, `Type`. For instance, `Int : Type(64_bits)` would be well typed, `String : Type(32_bits)` would be ill typed (assume `String`s are bigger than 32 bits). In the previous examples, `r` was an implicit parameter.

`Either` is parameterized by `data_rep`, `A`, and `B`. `A` and `B` are marked to be of representation `data_rep` by passing `data_rep` to their types, `Type(data_rep)`. We want `data_rep` to always be known at compile time, so we use the square brackets around the parameter. Because the representation of `A` and `B` is known at compile time, the data can be stored flat and unboxed in the `data` field. Layout polymorphism gives us control over data representation, allowing us to avoid unnecessary boxing. Note that this *also* depends on staging, which allows us to enforce that `data_rep` is compile time known.

`tag` is an `enum`, which are like C enums. They're anonymous types.
```ml
struct Either : [data_rep: Rep] -> (A : Type(data_rep)) -> (B : Type(data_rep)) -> Type(r) where
    tag : enum { left, right }
    data : // minor example of dependent types
        match tag
            left => A
            right => B
        end
end
```

We also need functions on `Rep`s, tagged unions pad the data field to be able to fit a value of a `A` *or* `B`. We can do that with `largest`, which takes two `Rep`s and returns the larger one. Here, `String`s take up more space than `Int`s, so `largest(int_rep, string_rep)` will return `string_rep`. A type does not have to exactly fit its representation, its representation is allowed to be larger than what is actually needed to store the value, which is why this works.
```ml
val example : Either(largest(int_rep, string_rep), Int, String)
let example = Either { tag = left, data = 34 }
```
Say we replaced the call to `largest` with a call to `smallest`, which would return the smallest of the two representations, we would get an error like this:
```
Error: `String` is not of type `Type(int_rep)`.
Help: `String` is too big to fit in an `int_rep`
```

#### Staging

In previous examples, the square bracket syntax was used:
```ml
val id : [T : Type(r)] -> T -> T
```
This square bracket syntax is however, actually just sugar for staging. The above example is equivalent to this:
```ml
val id : comptime (T : comptime Type(r)) -> T -> T
```
Staging allows us to control *when* evaluation happens, at compile time or run time. Every type is annotated with its stage. The outer function in `id` as well as its parameter (`T`) will be fully evaluated at compile time. Here, staging is used to express monomorphization. Staging allows us to remove the overhead of abstraction.

> Every type is annotated with its stage.

You may have noticed that this is not true in the example. In `T -> T`, none of the `T`s are annotated with their stage, nor is the function type itself. That is because if the stage is not specified, it is implicitly made stage polymorphic. The above is equivalent to this:
```ml
val id : comptime (T : comptime Type(r)) -> s1 (s2 T -> s3 T)
```
`s1`, `s2`, and `s3` are implicit parameters of type `Stage`. Stages are values, and can be abstracted over. The `Stage` type has two values, `comptime` and `runtime`. Here is `id` with the implicit parameters made explicit:
```ml
val id : comptime (s1, s2, s3 : comptime Stage) -> comptime (T : comptime Type(r)) -> s1 (s2 T -> s3 T)
```
The monomorphized function `id` returns can be used at any stage. As an aside: `Stage`s must be `comptime`.

Staging is used to eliminate the overhead of abstraction. Polymorphism is one example, as staging was used above to express monomorphization. Another example is with higher order functions, where staging can be used to express inlining. Take this function:
```ml
val double : comptime (Int -> Int)
let double = fun x => x + x
```
The arrow itself is `comptime`, but its input and output are not. Calling this function will evaluate the function, but not its argument or body. The argument will be substituted into the body and the body into the call site.
```ml
double(4)
// becomes
4 + 4
```
Let's take a more complex example: `compose`. We'll use the square bracket syntax:
```ml
val compose : [B -> C] -> [A -> B] -> comptime (A -> C)
let compose = fun f, g => fun x => f(g(x)) 
```
The desugared version:
```ml
val compose : comptime (comptime (B -> C) -> comptime (comptime (A -> B) -> comptime (A -> C)))
let compose = fun f, g => fun x => f(g(x)) 
```
First, `compose` will be fully inlined, since these two arrows (the bold ones) are `comptime`:\
**`comptime`**`(comptime (B -> C) -> `**`comptime`**` (comptime (A -> B) -> comptime (A -> C)))`

Second, the higher order functions will be inlined as well, since these two arrows are `comptime`:\
`comptime (`**`comptime`**` (B -> C) -> comptime (`**`comptime`**` (A -> B) -> comptime (A -> C)))`

Third, the function that `compose` returns will be inlined, since this arrow is `comptime`:\
`comptime (comptime (B -> C) -> comptime (comptime (A -> B) -> `**`comptime`**` (A -> C)))`

Calling `compose`:
```ml
let double = fun x => x + x
let square = fun x => x * x

compose(double, square)(5)
```
Looks like this at runtime:
```ml
let double = fun x => x + x
let square = fun x => x * x

(5 * 5) + (5 * 5)
```
Although this example is small, this idea scales. Using staging, the overhead of higher order functions can be removed.

**TODO**: Show partially evaluating a DSL. Explain how staging shows why polymorphic recursion cannot be monomorphized. Explain how layout polymorphism and staging work together
