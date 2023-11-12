
# Doon Notation
One feature of MPIR is it's support for Do/On (Doon!) Notation. This allows you to make actions based on the return value of a function call, without needlessly creating a variable to store this in.

This is called using the `do` and `on` keywords.
1. `do` is used to call the desired function.
2. `on` **`literal`** `→` is used to match the result against a literal.

>    **do** Function Call<br>
     **on** True → show "result was True"<br>
     **on** False → show "result was False"