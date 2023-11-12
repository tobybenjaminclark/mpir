
# Doon Notation
In [MPIR](https://github.com/tobybenjaminclark/mpir), the  Do/On (Doon!) Notation facilitates conditional actions based on **pattern matching the return value of a function**, eliminating the need for an intermediate variable. The syntax involves using the `do` keyword for the function call and the `on` keyword followed by a literal to match the result. 
This is called using the `do` and `on` keywords.

1. `do` **`function`** is used to call the desired function.
2. `on` **`literal`** `→` is used to match the result against a literal.

example mpir code:
>    **do** IsGreaterThanTen(5)<br>
     **on** `True` → show "result was True"<br>
     **on** `False` → show "result was False"

**Doon**.


**Techy Explanation**

Doon Notation is a syntactic construct that enables conditional execution based on the return value of a function, removing the requirement, in other languages, for the intermediate storage of said value. The mechanism is instantiated through the `do` keyword, serving as the invocatory precursor to the pertinent function, and the subsequent on keyword, which is followed by a literal to facilitate direct matching against the resultant value.