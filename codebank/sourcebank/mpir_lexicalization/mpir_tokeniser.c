/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_lexicalization/mpir_tokeniser.h"

bool mpir_wchar_in_list(wchar_t target, const wchar_t *list)
{
    size_t list_size = wcslen(list);    /* ← Calculate the size of the list uses wchar.h function. */
    size_t list_index;                  /* ← Stores the index of the current list item for loop.   */

    for (list_index = 0; list_index < list_size; ++list_index)
    {
        if (target == list[list_index])
        {
            return true;
        }
    }
    return false;
}

int mpir_tokenise_process_buffer(mpir_lexer *lexer, mpir_token_type toktype)
{
    /* Clear the buffer, and submit to token processing! */
    return 0;
}

/**
 * @brief Consumes a character from the source file and appends it to the lexer's buffer.
 *
 * This function verifies if the next character in the input stream matches the expected character. If it does, the
 * function appends the character to the lexer's buffer and increments the current index. If the expected character is
 * not found, an error message is generated and an error code is returned. Additionally, it checks for buffer overflow
 * and handles it by returning an error code if the buffer is full.
 *
 * @param lexer A pointer to the MPIR lexer structure.
 * @param expected_character The character expected to be consumed from the input stream.
 * @return 0 on success, or an error code (ERROR_UNEXPECTED_CHARACTER or ERROR_BUFFER_OVERFLOW) on failure.
 */
int consume_character(mpir_lexer* lexer, wchar_t expected_character)
{
    /* Ensure the expected character is equal to the actual character */
    if ( expected_character != lexer->peek(lexer) && expected_character != NULL)
    {
        mpir_error("mpir_tokeniser: failed to consume character");
        return ERROR_UNEXPECTED_CHARACTER;
    }

    wprintf(L"%lc", expected_character);

    /* Check if buffer is full, if so, handle accordingly (e.g., resize or process the buffer) */
    if (lexer->current_index >= BUFFER_SIZE - 1)
    {
        /* Handle buffer overflow (if it happens). */
        fprintf(stderr, "Error: Buffer overflow\n");
        return ERROR_BUFFER_OVERFLOW;
    }

    /* Append the character to the buffer & increment the current index */
    lexer->buffer[lexer->current_index] = lexer->get(lexer);
    lexer->current_index++;

    return 0;
}

int consume_character_any(mpir_lexer* lexer)
{
    /* Check if buffer is full, if so, handle accordingly (e.g., resize or process the buffer) */
    if (lexer->current_index >= BUFFER_SIZE - 1)
    {
        /* Handle buffer overflow (if it happens). */
        fprintf(stderr, "Error: Buffer overflow\n");
        return ERROR_BUFFER_OVERFLOW;
    }

    /* Append the character to the buffer & increment the current index */
    lexer->buffer[lexer->current_index] = lexer->get(lexer);
    lexer->current_index++;

    return 0;
}

mpir_lexer* mpir_tokenise(const char* file_path)
{
    wchar_t current_character;  /* ← Current Character in file (wchar_t to support POSIX unicode.) */
    mpir_lexer *lexer;          /* ← Instance of the lexer we're using, stores all associated data */

    /* Instantiate a lexer instance, and instruct it to read from the filepath. */
    lexer = mpir_lexer_create(file_path);
    if(lexer == NULL){return NULL;}

    /* Get the next character & process it through the tokenisation algorithm. */
    while((current_character = lexer->get(lexer)) != WEOF)
    {
        consume_character(lexer, lexer->peek(lexer));
    }

    return lexer;
}


int mpir_tokenise_base_state(mpir_lexer* lxr)
{
    /* Handling Comments */
    if(consume_character(lxr, '/'))
    {
        if (consume_character(lxr, '/'))
        {
            while(lxr->peek(lxr) != '\n' && lxr->peek(lxr) != WEOF)
            {
                consume_character_any(lxr);
            }
            /* Process comment */
            mpir_tokenise_process_buffer(lxr, COMMENT);
        }
        else
        {
            /* Process operator */
            mpir_tokenise_process_buffer(lxr, OPERATOR);
        }
    }
}