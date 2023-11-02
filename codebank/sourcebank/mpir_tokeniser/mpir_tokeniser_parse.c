/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_tokeniser/mpir_tokeniser_parse.h"

mpir_token** parse_tokens_from_json(const char* json) {

    mpir_token** tokens = NULL;
    int token_count = 0;

    const char* delimiters = "{},\": \n\t";
    char* token = strtok((char*)json, delimiters);

    while (token != NULL) {
        if (strcmp(token, "type") == 0) {
            token = strtok(NULL, delimiters);
            printf("%s ", token);
            int type = atoi(token);

            tokens = realloc(tokens, (token_count + 1) * sizeof(mpir_token*));
            tokens[token_count] = malloc(sizeof(mpir_token));

            if (tokens[token_count] == NULL) {
                fprintf(stderr, "Memory allocation failed\n");
                exit(EXIT_FAILURE);
            }

            tokens[token_count]->type = type;
        } else if (strcmp(token, "lexeme") == 0) {
            token = strtok(NULL, delimiters);
            if (token != NULL && token[0] == '\"') {
                wchar_t lexeme[1024] = L"";

                while ((token = strtok(NULL, delimiters)) != NULL && token[strlen(token) - 1] != '\"') {
                    wchar_t token_wchar[128];
                    mbstowcs(token_wchar, token, strlen(token) + 1);
                    wcscat(lexeme, token_wchar);
                    wcscat(lexeme, L" ");
                }

                if (wcslen(lexeme) > 0 && lexeme[wcslen(lexeme) - 1] == L' ') {
                    lexeme[wcslen(lexeme) - 1] = L'\0';
                }

                wprintf(L"%ls \n", lexeme);

                wcscpy(tokens[token_count]->lexeme, lexeme);
            }
        } else if (strcmp(token, "line_index") == 0) {
            token = strtok(NULL, delimiters);
            tokens[token_count]->line_index = atol(token);
        } else if (strcmp(token, "column_index") == 0) {
            token = strtok(NULL, delimiters);
            tokens[token_count]->column_index = atol(token);
            token_count++;
        }
        token = strtok(NULL, delimiters);
    }

    return tokens;
}

mpir_token** parse_tokens_from_json_file(const char* filename)
{
    FILE* file = fopen(filename, "r");
    if (file == NULL) {
        perror("Error opening file");
        return NULL;
    }

    fseek(file, 0, SEEK_END);
    long file_size = ftell(file);
    fseek(file, 0, SEEK_SET);

    char* json = malloc(file_size + 1);
    fread(json, 1, file_size, file);
    json[file_size] = '\0';

    fclose(file);

    mpir_token** tokens = parse_tokens_from_json(json);

    free(json);
    return tokens;
}
