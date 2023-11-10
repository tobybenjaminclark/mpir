
-- Keywords
"using"
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
"end"

-- widely-used declarations
letter                      ::=         'a' | 'b' | ... | 'z' | 'A' | 'B' | ... | 'Z'
digit                       ::=         '0' | '1' | ... | '9'

type_identifier             ::=         normal_identifier
flag_identifier             ::=         normal_identifier

-- highest level non-terminal, everything 'stems' from here.
line_of_code                ::=         import_directive
                                        | function_declaration
                                        | function_declaration
                                        | where_section
                                        | type_declaration
                                        | type_parameter_declaration
lines_of_code               ::=         line_of_code | (line_of_code lines_of_code)

import_directive            ::=         "using " "'" relative_file_path "'" "\n"

-- function
--                                      KEYWORD IDENTIFIER KEYWORD (IDENTIFIER "->" IDENTIFIER)*
function_declaration        ::=         "func " function_identifier "::" function_io '\n'
function_identifier         ::=         ( letter | digit | symbol ) | ( identifier letter | digit | symbol) '\n'
function_io                 ::=         ( type_identifiers ("->"|"→") type_identifiers )
type_identifiers            ::=         None | type_identifier | type_identifiers ", " type_identifier

function_definition         ::=         "func " function_identifier parameter_list 
parameter                   ::=         ( letter | digit | symbol ) | ( identifier letter | digit | symbol)
parameter_list              ::=         parameter | (parameter ", " parameter_list) 

-- CFG Defines the syntax for declaring tag-associated documentatio section, starts with where:/suchthat:
-- Followed by n statements of 'tag' 'identifier' as 'docstring', which can be formulated into documentation.
where_section               ::=         ("where:" | "suchthat:") "\n" doc_definitions "endwhere;" "\n"
doc_definition              ::=         ("|" flag_identifier (identifier | None) " as " docstring "\n")
doc_definitions             ::=         doc_definition | doc_definitions doc_definition
letters                     ::=         letter | letters letter
docstring                   ::=         '`' letters '`'

arithmetic_expression       ::=         term | arithmetic_expression operator_sum term | arithmetic_expression operator_subtract term
term                        ::=         factor | term operator_multiply factor | term operator_divide factor
factor                      ::=         open_bracket expression close_bracket | number | identifier | function_call
function_call               ::=         function_name open_bracket argument_list close_bracket
argument_list               ::=         expression | argument_list ',' expression
number                      ::=         digit | ( number digit )

variable_identifier         ::=         ( letter | digit ) | ( variable_identifier letter | digit )
type_identifier             ::=         ( letter | digit ) | ( type_identifier letter | digit)

variable_definition         ::=         "let " variable_identifier " as " type_identifier
variable_declaration        ::=         "set " variable_identifier " as " arithmetic_expression

-- example (potentially) recursive definition list a: Int, b:listInt = [a, [b, NULL]]
type_declaration            ::=         "typedef " type_identifier type_parameters "::" base_type_identifier
type_parameter_declaration  ::=         "typedef " parameter ":" type_identifier optional_refinement
optional_refinement         ::=         ("|" open_brace refinement close_brace "\n") | "\n"
refinement                  ::=         formula

-- CFG to define propositional & predicate logic to be used to define explicit type
-- refinements. E.g. x:Int | x > 5 ^ x < 10 (range of integers from 5 to 10)
formula                     ::=         primitive_formula | ('¬' formula) | (formula connective formula) | (quantifier variable_identifier ":" formula)
primitive_formula           ::=         ( predicate '(' terms ')' ) | ( term comparator term )
comparator                  ::=         ( '>' | '<' | '<=' | '>=' | '==' | 'is')
terms                       ::=         (terms term) | term
term                        ::=         constant | variable
connective                  ::=         ("->" | "→") | ∧ | ∨ | ("↔" | '<->')
quantifier                  ::=         '∀' | '∃'
constant                    ::=         literal

-- Operators (These are tokens)
operator_multiply           ::=         '*'
operator_divide             ::=         '/'
operator_sum                ::=         '+'
operator_subtract           ::=         '-'
operator_power              ::=         '^'
open_bracket                ::=         '('
close_bracket               ::=         ')'
open_brace                  ::=         '{'
close_brace                 ::=         '}'