/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_tokeniser/mpir_tokeniser_write.h"


int mpir_tokeniser_write(mpir_lexer* lexer, const char* file_path)
{
    FILE *file;                     /* ← Pointer to the (not yet initialized) .mpirtok output file.   */
    mpir_token* current_token;      /* ← Pointer to the (currently NULL), current token struct        */
    short int add_comma;            /* ← Integer representing True/False on whether to add a comma    */
    int token_index;                /* ← Integer representing the index of the current token.         */
    int writing_failed;             /* ← Integer representing whether the file can be written         */

    /* Attempt to open the file in write mode */
    file = fopen(file_path, "w");
    if (file == NULL)
    {
        mpir_error("Tokenizer unable to write .mpirtok data, file could not be opened.");
        return 1;
    }

    fwprintf(file, L"<blockquote>", file);
    for(token_index = 0; token_index < lexer -> token_count; token_index++)
    {
        /* Write the current token to the file, if this fails, exit with a failure code */
        current_token = lexer->tokens[token_index];
        writing_failed = mpir_write_token_md(current_token, file);
        if(writing_failed){return 1;}
    }
    fwprintf(file, L"</blockquote>", file);

    /* Close the file & return */
    fclose(file);
    return 0;
}