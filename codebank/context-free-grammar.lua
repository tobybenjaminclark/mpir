
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
-- variable_name as type
-- variable_name is 1

-- pythonic syntax
-- x: int | x > 1 | x < 5
