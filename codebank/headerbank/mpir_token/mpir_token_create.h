/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_TOKEN_CREATE_H
#define MPIR_COMPILER_MPIR_TOKEN_CREATE_H

#include "../../headerbank/mpir_token/mpir_token.h"

/**
 * @brief Create, allocate & return a new token structure.
 *
 * This expression allocates memory for a new token structure, initializes its attributes, and returns
 * a pointer to the created token. Tokens are essential elements in the process of lexical analysis
 * (tokenization) within the compiler. They represent identifiable elements in the source code, such
 * as keywords, operators, identifiers, and literals.
 *
 * @param type The type of the token, indicating its category (e.g., keyword, identifier, etc.).
 * @param lexeme The lexical representation of the token, typically the characters in the source code.
 * @param line The line number in the source code where the token appears.
 *
 * @return A pointer to the newly created token structure, or NULL if memory allocation fails.
 *
 * @note The lexeme parameter should be a C-style string (character array) with a maximum length
 * of 50 characters. The lexeme is copied into the token structure, ensuring proper null-termination.
 *
 * @warning It is the caller's responsibility to free the allocated memory for the token structure.
 */
mpir_token* mpir_create_token(mpir_token_type type, const wchar_t lexeme[50], int line);

#endif
