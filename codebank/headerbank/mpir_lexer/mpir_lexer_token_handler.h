#ifndef MPIR_COMPILER_MPIR_LEXER_TOKEN_HANDLER_H
#define MPIR_COMPILER_MPIR_LEXER_TOKEN_HANDLER_H

#include <stdio.h>
#include <string.h>

#define MPIR_KEYWORDS {"::","func"}

int mpir_lexer_is_keyword(char* lexeme);
int mpir_lexer_process_lexemme(char* lexeme);

#endif //MPIR_COMPILER_MPIR_LEXER_TOKEN_HANDLER_H
