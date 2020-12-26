a 'functional systems language'

### `World`

problems:
1. at the low level, nearly everything has effects, even something as basic as calling a function mutates the stack.
2. because of problem 1, referential transparency could not be used at all. if everything has effects, no expressions are equivalent

how do we track effects in a fine grained way?

index `World` by the set of what states it carries, e.g `stack`, `heap`, or `system`\
allow for world division, `extractStack : World [stack, heap, system] -> (World [stack], World [heap, system])`

how do we solve problem 2?