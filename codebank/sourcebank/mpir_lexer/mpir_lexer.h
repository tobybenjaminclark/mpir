

#ifndef MPIR_COMPILER_MPIR_LEXER_H
#define MPIR_COMPILER_MPIR_LEXER_H

#include <stdio.h>
#include "../../headerbank/mpir_lexer/mpir_token.h"

typedef struct
{
    long int current_token_index;
    long int token_count;
    FILE *source_file;
    mpir_token *tokens;
} mpir_lexer;

#endif //MPIR_COMPILER_MPIR_LEXER_H
