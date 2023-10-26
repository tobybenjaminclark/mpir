/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_lexicalization/mpir_tokeniser.h"

bool mpir_wchar_in_list(wchar_t target, const wchar_t *list)
{
    size_t list_size = wcslen(list);
    size_t i;
    for (i = 0; i < list_size; ++i)
    {
        if (target == list[i])
        {
            return true;
        }
    }
    return false;
}

int mpir_tokenise_process_buffer(mpir_lexer *lexer)
{
    return 0;
}

int tokenise_character(mpir_lexer* lexer, wchar_t current_character)
{
    wprintf(L"%lc", current_character);
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
        tokenise_character(lexer, current_character);
    }

    return lexer;
}