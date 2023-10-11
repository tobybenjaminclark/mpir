
-- widely-used declarations
letter                      ::=         'a' | 'b' | ... | 'z' | 'A' | 'B' | ... | 'Z'
digit                       ::=         '0' | '1' | ... | '9'

-- function
function_declaration        ::=         "func " function_identifier "::" function_curry
function_identifier         ::=         ( letter | digit | symbol ) | ( identifier letter | digit | symbol)
function_curry              ::=         ( identifier ("->"|"→") identifier | function_curry)                              -- identifier here must be a type.

function_definition         ::=         "func " function_identifier parameter_list
parameter                   ::=         ( letter | digit | symbol ) | ( identifier letter | digit | symbol)
parameter_list              ::=         parameter | (parameter parameter_list)