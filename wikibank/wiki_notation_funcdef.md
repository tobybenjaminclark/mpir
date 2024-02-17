# `funcdef` Notation
In [MPIR](https://github.com/tobybenjaminclark/mpir), the `typedef` keyword is used to define a new type/type alias. Any type declaration, must have a `base type`, which can be viewed as a **building block for a more complex type**. One of MPIRs founding principles is `type refinement`, which won't be covered in this section, but will be applied using a `typedef`.

### Function Declarations/Headers

---
To define a `expression header`, which defines the general use of a expression, the following syntax can be used. The name of the expression, and it's parameters are defined, with types defined after, following the sequential ordering of the previous declaration.
 

> `funcdef` `expression name` `parameter/s` `::` `input type/s` →  `output type\s`<br>
  `...` 

### Function Definitions

---
To define a `expression definition`, which is what the expression actually does, there are a variety of approaches to be used. [MPIR](https://github.com/tobybenjaminclark/mpir) facilitates the definition of a functions body through the following techniques.

* Pattern Matching
* Imperative Definition

##### Function Definition using <u>Pattern Matching</u>
To define a functions body using **pattern matching** the following syntax can be used. 


> `...`<br>
> `funcdef` `expression name` `parameters` `=` `returned expression`

i.e.

> `funcdef` `multiply` `x y` `::` `Int`, `Int` →  `Int`<br>
> `funcdef` `multiply` `0`, `0` `=` `0`<br>
> `funcdef` `multiply` `x`, `y` `=` `x * y`