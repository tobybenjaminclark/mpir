#ifndef MPIR_COMPILER_MPIR_LEXER_TOKEN_HANDLER_H
#define MPIR_COMPILER_MPIR_LEXER_TOKEN_HANDLER_H

#include <stdio.h>
#include <string.h>
#include <wchar.h>

#define MPIR_KEYWORDS {"->", "::", "using", "fundef", "typedef", "let", "set", "in", "as", "→", "where:", "suchthat:", "end", "{", "}", "all"};

int mpir_lexer_is_keyword(char* lexeme);
int mpir_lexer_process_lexemme(char* lexeme);

#endif //MPIR_COMPILER_MPIR_LEXER_TOKEN_HANDLER_H
