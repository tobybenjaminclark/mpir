/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_lexicalization/mpir_lexer_add_token.h"

void mpir_lexer_append_token(mpir_lexer *lexer, mpir_token *token)
{

    // Check if the token array needs to be resized
    if (lexer->token_count % BUFFER_SIZE == 0)
    {
        lexer->tokens = (mpir_token **)realloc(lexer->tokens, (lexer->token_count + BUFFER_SIZE) * sizeof(mpir_token*));
        if (lexer->tokens == NULL)
        {
            fprintf(stderr, "Memory allocation error");
            exit(EXIT_FAILURE);
        }
    }

    // Add the token to the array
    lexer->tokens[lexer->token_count] = token;
    lexer->token_count++;
}