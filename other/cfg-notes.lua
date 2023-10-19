
-- variable_declaration
-- data type must be checked semantically, is the type default or has it been declared?
variable_declaration    ::= data_type identifier
variable_declaration    ::= data_type identifier '=' expression

identifier  :           ::= ( letter | digit ) | ( identifier letter | digit )
letter                  ::= 'a' | 'b' | ... | 'z' | 'A' | 'B' | ... | 'Z'
digit                   ::= '0' | '1' | ... | '9'

-- expression (works with function calls)
-- supports stuff like 'int x = int y = int z = 5'
expression              ::= variable_declaration | arithmetic_expression
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

-- json & normal syntax for declarations
-- var x as 10
-- doc x as "Variable to store car data?"

int x =
{
    var: 10
    doc: "Variable to store car data"
}

doc x as 10
set x as 5
set x as x + 1
-- not sure to use set/var here ^
-- right side of x must be typed same as left side
-- need to work this with refinements

-- local function add:
--  | returns a + b + c;
-- with
--  | a as int
--  | a as parameter 1
--  | b as int
--  | b as parameter 2
--  | c as int
--  | c as 5
-- endfunction

-- global type nat:
--  | {x: Int | x > 0}
-- with
--  | doc x as "natural-number"
-- endtype

-- Pipe syntax slightly differnt

-- local function add(a, b) -> Int
--      | return a + b + c
-- where:
--      | type a: Int :: a > 0
--      | type b: Int :: b > 0
--      | type c: Int :: c > 0
--      | set c as 10
-- endfunction

-- Pipe Syntax Type Decl. Differently

-- global type nat(a):
--      | a: Int :: a > 0
-- where:
--      | doc a as "natural-number"`
-- endtype

-- boolean checking of ==
-- could be 'is'

-- Natural Language Syntax
-- if x is True:
--      | do x

-- This is called contract programming

-- add :: Integer -> Integer -> Integer   --function declaration 
-- add x y =  x + y                       --function definition 
-- where
--  | doc x as "Integer 1"
--  | doc y as "Integer 2"
--  | doc as "Function to add 2 Integers"
--  | author as "github.com/tobybenjaminclark"

-- add32 :: Integer -> Integer -> Integer32
-- add32 x y | (add x y) < 32 -> add x y
--           | (add x y) > 31 -> 0
-- where
--  | doc x as "Integer 1"
--  | doc y as "Integer 2"
--  | doc as "Function to add 2 Integers, output a 32 Bit Integer"
--  | author as "Toby Benjamin Clark"

-- inbuilts
-- + - * / %
-- > <
-- head
-- tail
-- null
-- :: (append/prepend)
-- char -> ascii
-- ascii -> char
-- support tuple (fst/snd)

-- add :: Integer -> Integer -> Integer   --function declaration 
-- add x y =  x + y                       --function definition 
-- where
--  | doc x as "Integer 1"
--  | doc y as "Integer 2"
--  | doc as "Function to add 2 Integers"
--  | author as "github.com/tobybenjaminclark
-- end add

-- trycast <identifier>:Type into <identifier>:Type
-- on success -> do x
-- on failure -> do y

-- func functionname :: Type -> Type -> Type ...
-- func functionname parameters = result
-- where
--  | flag param as value
--  | flag as value
-- end functionname