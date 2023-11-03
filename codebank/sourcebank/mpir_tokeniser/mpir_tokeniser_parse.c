/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_tokeniser/mpir_tokeniser_parse.h"

mpir_token** parse_tokens_from_json(FILE* json) {

    wchar_t* buffer[256];
    wchar_t current;
    mpir_token** tokens;
    int state;
    int token_count = 0;

    tokens = NULL;

    /* Clear the buffer */
    (void)wmemset(buffer, L'\0', sizeof(buffer) / sizeof(wchar_t));

    while((current = fgetwc(json)) != WEOF)
    {
        if(current != L'"')
        {
            continue;
        }
        else
        {
            wprintf(L"%lc \n", current);
        }
    }
}

mpir_token** parse_tokens_from_json_file(const char* filename)
{
    FILE* file = fopen(filename, "r");
    if (file == NULL) {
        perror("Error opening file");
        return NULL;
    }

    mpir_token** tokens = parse_tokens_from_json(file);

    fclose(file);
    return tokens;
}
