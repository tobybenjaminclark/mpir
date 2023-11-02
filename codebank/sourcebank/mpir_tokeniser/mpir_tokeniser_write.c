/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_tokeniser/mpir_tokeniser_write.h"


int mpir_tokeniser_write(mpir_lexer* lexer, const char* file_path)
{
    FILE *token_file;

    token_file = fopen(file_path, "w");

    if (token_file == NULL)
    {
        mpir_error("Tokenizer unable to write .mpirtok data, file could not be opened.");
        return 1;
    }

    int token_index;
    int writing_failed;

    for(token_index = 0; token_index < lexer->token_count; token_index++)
    {
        writing_failed = mpir_write_token(lexer -> tokens[token_index], token_file);
        if(writing_failed){return 1;}
    }

    fclose(token_file);
    return 0;
}