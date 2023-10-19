
-- Keywords
"where:"
"suchthat:"
"funcdef"
"typedef"
"let"
"set"
"in"
"as"
"->"
"→"

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

-- CFG Defines the syntax for declaring tag-associated documentatio section, starts with where:/suchthat:
-- Followed by n statements of 'tag' 'identifier' as 'docstring', which can be formulated into documentation.
where_section               ::=         ("where:" | "suchthat:") "\n" doc_definitions "endwhere;" "\n"
doc_definition              ::=         ("|" identifier (identifier | None) " as " docstring "\n")
doc_definitions             ::=         doc_definition | doc_definitions doc_definition
letters                     ::=         letter | letters letter
docstring                   ::=         '`' letters '`'

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

-- example (potentially) recursive definition list a: Int, b:listInt = [a, [b, NULL]]
type_declaration            ::=         "typedef " type_identifier type_parameters "::" base_type_identifier
type_parameter_declaration  ::=         "typedef " parameter ":" type_identifier optional_refinement
optional_refinement         ::=         ("|" "{" refinement "}" "\n") | "\n"
refinement                  ::=         formula

-- This 100% needs testing.
formula                     ::=         primitive_formula | ('¬' formula) | (formula connective formula) | (quantifier variable_identifier " : " formula)
primitive_formula           ::=         ( predicate '(' terms ')' ) | ( term comparator term )
comparator                  ::=         ( '>' | '<' | '<=' | '>=' | '==' | 'is')
terms                       ::=         (term) | (terms term)
term                        ::=         constant | variable
connective                  ::=         ("->" | "→") | ∧ | ∨ | ("↔" | '<->')
quantifier                  ::=         '∀' | '∃'
constant                    ::=         literal
