/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_LEXER_H
#define MPIR_COMPILER_MPIR_LEXER_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../mpir_token/mpir_token.h"
#include "../../headerbank/mpir_misc/mpir_warnings.h"

#define BUFFER_SIZE 127

/**
 * @brief Struct representing a lexer for tokenizing source code.
 *
 * The `mpir_lexer` struct is responsible for maintaining the state of lexical analysis
 * of a source code file. It tracks the current position in the file, the size of the buffer,
 * the number of tokens processed, the current line and column numbers, and other relevant
 * information for tokenization.
 */
typedef struct
{
    unsigned long int current_index;
    unsigned long int buffer_size;
    unsigned long int token_count;
    unsigned long int line_number;
    unsigned int column_number;

    FILE *source_file;
    mpir_token **tokens;
    char current_char;
    char buffer[BUFFER_SIZE];
} mpir_lexer;


/**
 * @brief Attempts to create an MPIR lexer for tokenizing an .mpir input file.
 *
 * This function initializes an MPIR lexer structure used for tokenizing a source file in the MPIR compiler.
 * The lexer processes the specified file, breaking it down into individual tokens that are used in the
 * subsequent stages of the MPIR compilation process. Please free this structure using mpir_lexer_free()
 * function after use to avoid memory leaks.
 *
 * @param filepath The path to the input file to be tokenized.
 *
 * @return A pointer to the newly created MPIR lexer structure, or NULL in case of failure.
 *         If memory allocation fails, an error message is logged, and NULL is returned.
 *         If the specified file cannot be opened, an error message is logged, the allocated memory is freed, and NULL is returned.
 */
mpir_lexer* mpir_lexer_create(const char *filepath);


/**
 * @brief Frees the memory allocated for the given MPIR lexer structure and its associated resources.
 *
 * This function deallocates memory used by the provided MPIR lexer structure. It closes the source file,
 * frees the buffer used for constructing token lexemes, and releases memory occupied by individual Token
 * structures in the lexer. Finally, it frees the token array itself and sets the pointer to NULL.
 *
 * @param lexer A pointer to the MPIR lexer structure to be deallocated.
 *
 * @remark Ensure that the provided MPIR lexer structure is no longer used after calling this function, as
 * accessing the structure or any of its members after deallocation results in undefined behavior, as the
 * structure no longer exists.
 */
void mpir_lexer_free(mpir_lexer *lexer);

#endif
