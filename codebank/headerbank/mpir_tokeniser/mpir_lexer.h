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
#include <locale.h>
#include <wchar.h>

#include "../mpir_token/mpir_token.h"
#include "../../headerbank/mpir_misc/mpir_warnings.h"

#define BUFFER_SIZE 127

/* Forward Declaration (for use in struct declaration) */
struct mpir_lexer;



/**
 * @brief Struct representing a lexer for tokenizing source code.
 *
 * The `mpir_lexer` struct is responsible for maintaining the state of lexical analysis
 * of a source code file. It tracks the current position in the file, the size of the lexeme,
 * the number of tokens processed, the current line and column numbers, and other relevant
 * information for tokenization.
 */
struct mpir_lexer
{
    unsigned long int current_index;
    unsigned long int buffer_size;
    unsigned long int token_count;
    unsigned long int line_number;
    unsigned int column_number;

    FILE *source_file;
    mpir_token **tokens;
    wchar_t current_character;
    wchar_t lexeme[BUFFER_SIZE];

    /* Function Pointers */
    wchar_t (*get)(struct mpir_lexer *lexer);
    wchar_t (*peek)(struct mpir_lexer *lexer);
} ;

typedef struct mpir_lexer mpir_lexer;

/**
 * @brief Reads the next wide character from the input file of the lexer.
 *
 * This function reads the next wide character from the input file associated
 * with the given lexer. If successful, it advances the file pointer to the
 * next character. If the end of the file is reached or an error occurs, it
 * returns the wide end-of-file character (WEOF).
 *
 * @param lexer Pointer to the mpir_lexer structure.
 * @return Next wide character, or WEOF on end of file or error.
 */
wchar_t mpir_lexer_get(mpir_lexer *lexer);



/**
 * @brief Peeks at the next wide character from the input file without consuming it.
 *
 * This function reads the next wide character from the input file associated
 * with the given lexer, but does not advance the file pointer. It allows
 * examining the next wide character without consuming it.
 *
 * @param lexer Pointer to the mpir_lexer structure.
 * @return Next wide character, or WEOF on end of file or error.
 */
wchar_t mpir_lexer_peek(mpir_lexer *lexer);



/**
 * @brief Opens and initializes a file with POSIX encoding.
 *
 * This function attempts to open the specified file in read mode. If the file opening operation fails, it displays an
 * error message using the mpir_error function and returns NULL. If successful, it sets the locale to the 'C' Locale
 * (POSIX/classic), enabling wide character handling, and returns a pointer to the opened file for further lexing
 * operations. User is responsible for freeing the file pointer after use.
 *
 * @param file_name A pointer to a string containing the name of the file to be opened.
 * @return A pointer to a FILE object representing the opened file, or NULL if an error occurs.
 */
FILE* mpir_lexer_open_file(const char* file_name);



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
 * frees the lexeme used for constructing token lexemes, and releases memory occupied by individual Token
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
