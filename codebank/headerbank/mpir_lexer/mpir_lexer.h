

#ifndef MPIR_COMPILER_MPIR_LEXER_H
#define MPIR_COMPILER_MPIR_LEXER_H

#include <stdio.h>
#include "mpir_token.h"

typedef struct
{
    unsigned long int current_index;    // Current character index
    unsigned long int buffer_size;      // Size of the buffer
    unsigned long int token_count;      // Number of tokens in the list
    unsigned long int line_number;      // Current line number in the source file
    unsigned int column_number;         // Current column number in the source file

    FILE *source_file;                  // Pointer to the open source file
    Token *tokens;                      // Current list of tokens
    char current_char;                  // Current character being processed
    char *buffer;                       // Buffer for constructing token lexemes dynamically
} mpir_lexer;


#endif //MPIR_COMPILER_MPIR_LEXER_H
