
function_declaration        ::=         "func " function_identifier "::" function_curry
function_identifier         ::=         ( letter | digit | symbol ) | ( identifier letter | digit | symbol)
function_curry              ::=         ( identifier "->" identifier | function_curry)
letter                      ::=         'a' | 'b' | ... | 'z' | 'A' | 'B' | ... | 'Z'
digit                       ::=         '0' | '1' | ... | '9'
