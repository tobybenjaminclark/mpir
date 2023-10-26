/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_lexicalization/mpir_lexer.h"




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
wchar_t mpir_lexer_get(mpir_lexer* lexer)
{
    return (lexer && lexer->source_file) ? fgetwc(lexer->source_file) : WEOF;
}



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
wchar_t mpir_lexer_peek(mpir_lexer* lexer)
{
    wchar_t character = mpir_lexer_get(lexer);
    ungetwc(character, lexer->source_file);
    return character;
}



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
FILE* mpir_lexer_open_file(const char* file_name)
{
    /* File pointer that is going to be used to store the current file */
    FILE *input;

    /*
     * Sets the current locale to the 'C' Locale, a.k.a. 'POSIX'/'classic'
     * POSIX is a superset of the default ASCII character set, allowing for special characters beyond this range, such
     * as special symbols (∀/∃), & emojis. This requires the use of wide character handling using the wchar_t datatype.
     */
    (void)setlocale(LC_CTYPE,"C");

    /*
     * Attempt to open file in readmode. In the event of an error, display the error using the mpir_error function, then
     * return null. If successful, return the input file.
     */
    if ((input = fopen(file_name,"r")) == NULL)
    {
        (void)mpir_error("mpir_tokeniser: failed to open file %s", file_name);
        return NULL;
    }
    else
    {
        return input;
    }
}



/**
 * @brief Attempts to create an MPIR lexer for tokenizing an .mpir input file.
 *
 * This function initializes an MPIR lexer structure used for tokenizing a source file in the MPIR compiler. The lexer
 * processes the specified file, breaking it down into individual tokens that are used in the subsequent stages of the
 * MPIR compilation process. Please free this structure using the mpir_lexer_free() function after use.
 *
 * @param filepath The path to the input file to be tokenized.
 *
 * @return A pointer to the newly created MPIR lexer structure, or NULL in case of failure.
 *         If memory allocation fails, an error message is logged, and NULL is returned.
 *         If the specified file cannot be opened, an error message is logged, the allocated memory is freed, and NULL is returned.
 */
mpir_lexer* mpir_lexer_create(const char *filepath)
{
    /* Allocate memory for the lexer */
    mpir_lexer *lexer = (mpir_lexer*)malloc(sizeof(mpir_lexer));

    /* Check for memory allocation failure */
    if (lexer == NULL)
    {
        mpir_error("Out of memory, failed to allocate MPIR Lexer.");
        return NULL;
    }

    /*
     * Setup default lexer values
     */
    lexer->current_index = 0;
    lexer->buffer_size = 0;
    lexer->token_count = 0;
    lexer->line_number = 1;
    lexer->column_number = 1;
    lexer->current_character = '\0';
    lexer->tokens = NULL;

    /* Setup Function pointers for get & peek functions */
    lexer->get = (wchar_t (*)(struct mpir_lexer *)) mpir_lexer_get;
    lexer->peek = (wchar_t (*)(struct mpir_lexer *)) mpir_lexer_peek;

    /* Open the source file */
    lexer->source_file = mpir_lexer_open_file(filepath);

    /* Check if file opening is successful */
    if (lexer->source_file == NULL)
    {
        free(lexer);
        return NULL;
    }

    return lexer;
}



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
void mpir_lexer_free(mpir_lexer *lexer)
{
    /* Ensure MPIR lexer structure is non-NULL */
    if (lexer == NULL)
    {
        mpir_warn("Attempted to free a NULL lexer structure.");
        return;
    }

    /* Free the buffer used for constructing token lexemes */
    if (lexer->source_file != NULL)
    {
        fclose(lexer->source_file);
    }
    else
    {
        mpir_warn("Attempted to close a NULL file.");
        return;
    }

    /* Free each Token in the lexer, and then free and null the token array */
    unsigned long int i;
    for (i = 0; i < lexer->token_count; ++i)
    {
        free(lexer->tokens[i]);
    }
    free(lexer->tokens);
    lexer->tokens = NULL;

    /* Free the lexer structure itself */
    free(lexer);
}
