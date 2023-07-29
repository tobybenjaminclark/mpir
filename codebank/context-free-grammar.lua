
-- variable_declaration
-- data type must be checked semantically, is the type default or has it been declared?
variable_declaration    ::= data_type identifier
variable_declaration    ::= data_type identifier '=' expression

identifier  :           ::= ( letter | digit ) | ( identifier letter | digit )
letter                  ::= 'a' | 'b' | ... | 'z' | 'A' | 'B' | ... | 'Z'
digit                   ::= '0' | '1' | ... | '9'

-- expression (works with function calls)
-- supports stuff like 'int x = int y = int z = 5'
expression              ::=  variable_declaration | arithmetic_expression
arithmetic_expression   ::= term | arithmetic_expression '+' term | arithmetic_expression '-' term
term                    ::= factor | term '*' factor | term '/' factor
factor                  ::= '(' expression ')' | number | identifier | function_call
function_call           ::= function_name '(' argument_list ')'
argument_list           ::= expression | argument_list ',' expression
number                  ::= digit | ( number digit )

-- variable typing & declarations

-- nat lang syntax
-- variable_name as base-type
-- variable_name is <rule>

-- pythonic syntax
-- x: int | x > 1 | x < 5

-- quantum syntax
-- x is in a superposition > 2 and < 3 but is not known until observed (read from memory)
-- x: int | { x > 1 } | { x < 5 }

-- maybe use feta or other symbol to represent x?

-- contextual type annotations
-- Can extend types to add relevant stuff for that variable e.g.
-- speed: int
-- speed <- "Speed of the car in km/h"
-- speed = 5

-- pre & post conditions on functions
-- function divide(a: int, b: int != 0): number where { number is integer } {
--    // ... function implementation
-- }