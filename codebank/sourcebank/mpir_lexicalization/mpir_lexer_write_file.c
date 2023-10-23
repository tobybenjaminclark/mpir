
// GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark
// This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
// License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.

#include "../../headerbank/mpir_lexicalization/mpir_lexer_write_file.h"

/// @brief Writes the tokens from an mpir_lexer to a file.
///
/// This function writes the tokens stored in the given mpir_lexer structure
/// to a file specified by the provided file path.
///
/// @param lexer A pointer to the mpir_lexer structure containing tokens to be written.
/// @param file_path The file path where the tokens will be written.
///
/// @return Returns 0 on success, and 1 on failure.
///
int mpir_lexer_write_file(mpir_lexer* lexer, const char* file_path)
{
    FILE *token_file;

    // Open file in write mode
    token_file = fopen(file_path, "w");

    // Check if the file is successfully opened
    if (token_file == NULL)
    {
        mpir_error("Tokenizer unable to write .mpirtok data, file could not be opened.");
        return 1;
    }

    size_t token_count = sizeof(lexer -> tokens) / sizeof(lexer -> tokens[0]);
    int token_index;
    int writing_failed;

    for(token_index = 0; token_index < lexer->token_count; token_index++)
    {
        printf("Writing to file! Token %d of %d\n", token_index, lexer->token_count);
        writing_failed = mpir_write_token(lexer -> tokens[token_index], token_file);
        if(writing_failed){return 1;}
    }

    fclose(token_file);
    return 0;
}