

#ifndef MPIR_COMPILER_MPIR_LEXER_H
#define MPIR_COMPILER_MPIR_LEXER_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BUFFER_SIZE 127
#include "mpir_token.h"


typedef struct
{
    unsigned long int current_index;    // Current character index
    unsigned long int buffer_size;      // Size of the buffer
    unsigned long int token_count;      // Number of tokens in the list
    unsigned long int line_number;      // Current line number in the source file
    unsigned int column_number;         // Current column number in the source file

    FILE *source_file;                  // Pointer to the open source file
    mpir_token **tokens;                // Current list of tokens
    char current_char;                  // Current character being processed
    char buffer[BUFFER_SIZE];           // Buffer for constructing token lexemes dynamically
} mpir_lexer;

mpir_lexer* mpir_lexer_create(const char *filepath);
void mpir_lexer_free(mpir_lexer *lexer);
int mpir_lexer_tokenize(mpir_lexer *lexer);

#endif //MPIR_COMPILER_MPIR_LEXER_H
