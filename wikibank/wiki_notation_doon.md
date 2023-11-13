
# `do`/`on` Notation
In [MPIR](https://github.com/tobybenjaminclark/mpir), the  Do/On (Doon!) Notation facilitates <u>conditional actions</u> based on **pattern matching the return value of a function**, eliminating the need for an intermediate variable. The syntax involves using the `do` keyword for the function call and the `on` keyword followed by a literal to match the result. 
This is called using the `do` and `on` keywords.

1. `do` **`function`** is used to call the desired function.
2. `on` **`literal`** `→` is used to match the result against a literal.

The following is an example of a `do`/`on` implementation. If the returned value of the `function call` is `True`, then 'result was True' is shown to the console. If the returned value of the `function call` is `False` then 'result was False' is shown.
>    **do** `function call`<br>
     **on** `True` → `show` "result was True"<br>
     **on** `False` → `show` "result was False"

[MPIR](https://github.com/tobybenjaminclark/mpir) offers the `do`/`on` syntax, to encourage the implementation and catching of maintainable error codes in functions. This can be seen as a streamlined alternative to the following code, which uses traditional `if`/`else` syntax. 

>    `type` `variable` = `function call`<br>
     `if` `variable` == `True`:  `show` "result was True"<br>
     `if` `variable` == `True`:  `show` "result was False"

