#ifndef MPIR_COMPILER_MPIR_LEXER_TOKEN_TYPER_H
#define MPIR_COMPILER_MPIR_LEXER_TOKEN_TYPER_H

#include <string.h>

#define MPIR_KEYWORDS {"::","func"}

int mpir_lexer_is_keyword(char* lexeme);

#endif //MPIR_COMPILER_MPIR_LEXER_TOKEN_TYPER_H
