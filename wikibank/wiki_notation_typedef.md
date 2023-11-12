
# `typedef` Notation
In [MPIR](https://github.com/tobybenjaminclark/mpir), the `typedef` keyword is used to define a new type/type alias. Any type declaration, must have a `base type`, which can be viewed as a **building block for a more complex type**. One of MPIRs founding principles is `type refinement`, which won't be covered in this section, but will be applied using a `typedef`.

### Type Alias Declarations & Definitions

---
To define a `type alias`, which can be seen as **declaring a new name for an existing type**, the following syntax can be used.

> `typedef` `type name` `parameter/s` `::` `base type`<br>
  `typedef` `parameter` `:` `base type`

This is an example declaration of a new type `Integer`, which acts as an **alias** to the primitive/base type `Int`, with no additional refinement.

> `typedef` `Integer` `i` `::` `Int`<br>
  `typedef` `i` `:` `Int`

### Type Refinement Declarations & Definitions

---
To define a `type refinement`, which can be seen as **declaring a new type, as a set of constraints on another type**, the optional refinement clause of the `typedef` declaration can be used, this can be seen in the following syntax.

>   `typedef` `type name` `parameter/s` :: `base type`<br>
    `typedef` `parameter` : `base type` `{` `refinement` `}`

This is an example declaration of a new type `PositiveInteger`, which uses the base type `Int`, with a **refinement** that all values of `i` must be greater than zero, hence all values of `i` must be positive.

Refinements on types are expressed using `propositional`/`predicate` notation, more about this can be seen under the type refinement section. **Type Refinement is a powerful tool**, that can and should be used to express complex data types for enhanced code validation.

> `typedef` `PositiveInteger` `i` `::` `Int`<br>
  `typedef` `i` `:` `Int` `{` `∀i : i > 0` `}`
