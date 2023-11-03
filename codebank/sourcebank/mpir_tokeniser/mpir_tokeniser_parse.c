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
    state = STATE_PROCESSING_TOKEN_COUNT;

    /*
     * Pre Token
     * Token Count
     * In token
     * Key
     * Value
     */
    /* Clear the buffer */
    (void)wmemset(buffer, L'\0', sizeof(buffer) / sizeof(wchar_t));

    const wchar_t* target_string = L"oken count";

    while ((current = fgetwc(json)) != WEOF) {
        switch (state) {
            case (STATE_PROCESSING_TOKEN_COUNT):
                wprintf(L"%lc \n", current);
                if (current == L'o') {
                    const wchar_t* found = wcsstr(target_string, L"oken count\" :");
                    if (found != NULL) {
                        // Match found, do something
                        printf("Match found!\n");
                        state = 3;
                        continue;
                    }
                }
                break;

            case(3):
                wprintf(L"%lc \n", current);
                break;
            case(4):
                break;
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
