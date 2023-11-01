/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_TOKEN_H
#define MPIR_COMPILER_MPIR_TOKEN_H

#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include "../mpir_misc/mpir_warnings.h"


typedef enum
{
    COMMENT,
    NUMERICAL_LITERAL,
    STRING_LITERAL,
    OPERATOR,
    IDENTIFIER,
    KEYWORD
} mpir_token_type;



typedef struct
{
    /* Type of the token (e.g., number, operator, identifier, etc.) */
    mpir_token_type type;

    /* Lexeme of the token (actual value as a string) */
    char lexeme[128];

    /* Line number in the source code where the token appears */
    unsigned long int line_index;
    unsigned long int column_index;

} mpir_token;

/**
 * @brief Writes an MPIR token to a specified file.
 *
 * This function writes the given MPIR token to the provided file stream in a specific format. The token type, lexeme,
 * line index, and column index are written to the file in the following order:
 * - Token type (e.g., NUMERICAL_LITERAL, STRING_LITERAL, OPERATOR, IDENTIFIER, KEYWORD)
 * - Token lexeme (string representation of the token)
 * - Token line index (line number in the source file where the token is located)
 * - Token column index (column number in the source file where the token starts)
 *
 * The file must be opened in an appropriate mode before calling this function. It is the caller's responsibility to
 * manage file opening and closing. The function also performs basic error checking, ensuring that the file is already
 * open before writing the token data. Token end and start points are symbolized by START_TOK & END_TOK
 *
 * @param token A pointer to the MPIR token structure containing information about the token to be written.
 * @param file A pointer to the FILE structure representing the file where the token data will be written.
 * @return 0 indicating success, or 1 indicating failure.
 */
int mpir_write_token(mpir_token* token, FILE* file);

#endif
