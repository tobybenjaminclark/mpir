
-- Keywords
"using"
"return"
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

-- expression KEYWORD IDENTIFIER KEYWORD (IDENTIFIER "->" IDENTIFIER)*
function_declaration        ::=         "funcdef" function_identifier "::" function_io '\n'
function_identifier         ::=         ( letter | digit | symbol ) | ( identifier letter | digit | symbol) '\n'
function_io                 ::=         ( type_identifiers ("->"|"→") type_identifiers )
type_identifiers            ::=         None | type_identifier | type_identifiers comma type_identifier


-- Function Definition (body)
function_definition_header  ::=         function_identifier parameter_list ':' '\n'
parameter_list              ::=         identifier | parameter_list ',' identifier
identifiers                 ::=         identifier | ( identifier identifiers )
function_definition_body    ::=         line_of_code
let_assignment              ::=         'let' identifier 'as' type_identifier '\n'
set_assignment              ::=         'set' identifier 'as' expression '\n'
function_call_line          ::=         function_call '\n'
inbuilt_call                ::=         identifier identifiers
trycast_line                ::=         'trycast' identifier 'into' identifier '\n'
do_line                     ::=         'do' function_call '\n'
on_line                     ::=         'on' literal '->' line_of_code
imperative_statement        ::=         set_assignment | let_assignment | function_call_line | inbuilt_call | trycast_line | do_line | on_line
imperative_statements       ::=         imperative_statement | imperative_statements imperative_statement
imperative_definition       ::=         function_identifier parameter_list '=' imperative_statements

-- Supports do/on notation
-- Pattern Matching Syntax
pattern_match               ::=         function_identifier parameter_list '=' expression
pattern_parameter           ::=         (( letter | digit | symbol ) | (parameter letter | digit | symbol)) | literal
pattern_parameter_list      ::=         pattern_parameter | (pattern_parameter comma pattern_parameter_list)

-- CFG Defines the syntax for declaring tag-associated documentatio section, starts with where:/suchthat:
-- Followed by n statements of 'tag' 'identifier' as 'docstring', which can be formulated into documentation.
where_section               ::=         ("where:" | "suchthat:") "\n" doc_definitions "endwhere;" "\n"
doc_definition              ::=         ("|" flag_identifier (identifier | None) " as " docstring "\n")
doc_definitions             ::=         doc_definition | doc_definitions doc_definition
letters                     ::=         letter | letters letter
docstring                   ::=         '`' letters '`'

arithmetic_expression       ::=         term | arithmetic_expression operator_sum term | arithmetic_expression operator_subtract term
term                        ::=         factor | term operator_multiply factor | term operator_divide factor
factor                      ::=         open_bracket expression close_bracket | numerical_literal | identifier | function_call | string_literal
function_call               ::=         function_name open_bracket argument_list close_bracket
argument_list               ::=         expression | argument_list comma expression
string_literal              ::=         '"' characters '"'
characters                  ::=         character | characters character
numerical_literal           ::=         ('-' | ε) digits ( ('.' digits) | ε )
digits                      ::=         digit | ( digits digit )

variable_identifier         ::=         ( letter | digit ) | ( variable_identifier letter | digit )
type_identifier             ::=         ( letter | digit ) | ( type_identifier letter | digit)

variable_definition         ::=         "let " variable_identifier " as " type_identifier
variable_declaration        ::=         "set " variable_identifier " as " arithmetic_expression

-- example (potentially) recursive definition list a: Int, b:listInt = [a, [b, NULL]]
type_declaration            ::=         "typedef" type_identifier type_parameters "::" base_type_identifier
type_parameter_declaration  ::=         "typedef" parameter ":" type_identifier optional_refinement
optional_refinement         ::=         ("|" open_brace refinement close_brace "\n") | "\n"
refinement                  ::=         formula

-- CFG to define propositional & predicate logic to be used to define explicit type
-- refinements. E.g. x:Int | x > 5 ^ x < 10 (range of integers from 5 to 10)
formula                     ::=         primitive_formula | ('¬' formula) | (formula connective formula) | (quantifier variable_identifier ":" formula)
primitive_formula           ::=         ( predicate open_bracket terms close_bracket ) | ( term comparator term )
comparator                  ::=         ( operator_gt | operator_lt | operator_lteq | operator_gteq | operator_eq )
terms                       ::=         (terms term) | term
term                        ::=         constant | variable
connective                  ::=         arrow | operator_and | operator_or | bidirectional_arrow
quantifier                  ::=         universal_quantifier | existential_quantifier
constant                    ::=         literal

-- Connectives
operator_arrow              ::=         "->" | "→"
operator_bi_arrow           ::=         "↔" | '<->'
operator_and                ::=         '^'
operator_or                 ::=         '∨'


-- Boolean Comparator Operators
operator_eq                 ::=         '==' | 'is'
operator_gt                 ::=         '> '
operator_lt                 ::=         '<'
operator_gteq               ::=         '>='
operator_lteq               ::=         '<='


-- Operators (These are tokens)
operator_multiply           ::=         '*'
operator_divide             ::=         '/'
operator_sum                ::=         '+'
operator_subtract           ::=         '-'
operator_power              ::=         '^'
universal_quantifier        ::=         '∀'
existential_quantifier      ::=         '∃'

-- Brackets
open_bracket                ::=         '('
close_bracket               ::=         ')'
open_brace                  ::=         '{'
close_brace                 ::=         '}'

-- Comma
comma                       ::=         ','
pipe                        ::=         '|'
colon                       ::=         ':'
double_colon                ::=         '::'