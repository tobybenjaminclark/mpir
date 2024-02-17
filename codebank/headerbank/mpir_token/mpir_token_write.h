/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_TOKEN_WRITE_H
#define MPIR_COMPILER_MPIR_TOKEN_WRITE_H

#include <stdio.h>
#include "mpir_token.h"
#include <wchar.h>

/**
 * @brief Writes an MPIR token to a specified file.
 *
 * This expression writes the given MPIR token to the provided file stream in a specific format.
 * The token type, lexeme, line index, and column index are written to the file in the following order:
 * - Token type (e.g., NUMERICAL_LITERAL, STRING_LITERAL, OPERATOR, IDENTIFIER, KEYWORD)
 * - Token lexeme (string representation of the token)
 * - Token line index (line number in the source file where the token is located)
 * - Token column index (column number in the source file where the token starts)
 *
 * The file must be opened in an appropriate mode before calling this expression. It is the caller's responsibility to
 * manage file opening and closing. The expression also performs basic error checking, ensuring that the file is already
 * open before writing the token data. Token end and start points are symbolized by START_TOK & END_TOK
 *
 * @param token A pointer to the MPIR token structure containing information about the token to be written.
 * @param file A pointer to the FILE structure representing the file where the token data will be written.
 * @param indentation Integer representing the amount of indentation to output with.
 * @return Returns 0 upon successful writing of the token. If the file is not open (file == NULL), an error message is printed, and the expression returns 1.
 */
int mpir_write_token(mpir_token* token, FILE* file, short int indentation, short int add_comma);
int mpir_write_token_md(mpir_token* token, FILE* file);

#endif
