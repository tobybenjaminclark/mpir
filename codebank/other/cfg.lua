
-- widely-used declarations
letter                      ::=         'a' | 'b' | ... | 'z' | 'A' | 'B' | ... | 'Z'
digit                       ::=         '0' | '1' | ... | '9'

-- function
function_declaration        ::=         "func " function_identifier "::" function_curry '\n'
function_identifier         ::=         ( letter | digit | symbol ) | ( identifier letter | digit | symbol) '\n'
function_curry              ::=         ( identifier ("->"|"→") identifier | function_curry)                              -- identifier here must be a type.

function_definition         ::=         "func " function_identifier parameter_list 
parameter                   ::=         ( letter | digit | symbol ) | ( identifier letter | digit | symbol)
parameter_list              ::=         parameter | (parameter ", " parameter_list) 

where_section               ::=         ("where:" | "such that:") "\n" doc_definitions "endwhere" "\n"
doc_definitions             ::=         "|" identifier (identifier | None) " as " string/whatever? "\n" recursive more     -- do doc definitions more

arithmetic_expression       ::=         term | arithmetic_expression '+' term | arithmetic_expression '-' term
term                        ::=         factor | term '*' factor | term '/' factor
factor                      ::=         '(' expression ')' | number | identifier | function_call
function_call               ::=         function_name '(' argument_list ')'
argument_list               ::=         expression | argument_list ',' expression
number                      ::=         digit | ( number digit )

variable_identifier         ::=         ( letter | digit ) | ( variable_identifier letter | digit )
type_identifier             ::=         ( letter | digit ) | ( type_identifier letter | digit)

variable_definition         ::=         "let " variable_identifier " as " type_identifier
variable_declaration        ::=         "set " variable_identifier " as " arithmetic_expression