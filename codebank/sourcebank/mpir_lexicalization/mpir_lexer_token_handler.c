/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_lexicalization/mpir_lexer_token_handler.h"

int mpir_lexer_has_newline(const char* lexeme)
{
    int i = 0;
    for (i = 0; lexeme[i] != '\0'; ++i)
    {
        if (lexeme[i] == '\n')
        {
            return 1;
        }
    }
    return 0;
}

int mpir_lexer_has_comma(const char* lexeme)
{
    int i = 0;
    for (i = 0; lexeme[i] != '\0'; ++i)
    {
        if (lexeme[i] == ',')
        {
            return 1;
        }
    }
    return 0;
}

int mpir_lexer_is_colon(char* lexeme)
{
    int i = 0;
    for (i = 0; lexeme[i] != '\0'; ++i)
    {
        if (lexeme[i] == ':')
        {
            return 1;
        }
    }
    return 0;
}

int mpir_lexer_is_pipe(char* lexeme)
{
    int i = 0;
    for (i = 0; lexeme[i] != '\0'; ++i)
    {
        if (lexeme[i] == '|')
        {
            return 1;
        }
    }
    return 0;
}

int mpir_lexer_is_comment(char* lexeme)
{
    int size = sizeof(lexeme) / sizeof(lexeme[0]);
    if(size > 2)
    {
        if (lexeme[0] == lexeme[1] && lexeme[0] == '/')
        {
            return 1;
        }
    }
    return 0;
}

int mpir_lexer_is_operator(char* lexeme)
{
    const char* operators[] = {"+", "-", "*", "/", "%", "=="};
    int numOperators = sizeof(operators) / sizeof(operators[0]);

    int operator_index = 0;
    for (operator_index = 0; operator_index < numOperators; ++operator_index)
    {
        if (strcmp(lexeme, operators[operator_index]) == 0)
        {
            return 1;
        }
    }

    return 0;
}

int mpir_lexer_is_keyword(char* lexeme)
{
    char * x [] = MPIR_KEYWORDS;
    int len = sizeof(x)/sizeof(x[0]);
    int i;

    for(i = 0; i < len; ++i)
    {
        if(!strcmp(x[i], lexeme))
        {
            return 1;
        }
    }
    return 0;
}

int mpir_lexer_is_string_literal(char* lexeme)
{
    if (strlen(lexeme) > 0)
    {
        char first = lexeme[0];
        char last = lexeme[strlen(lexeme) - 1];
        if (first == last && (first == 34 || first == 39    ))
        {
            return 1;
        }
    }
    return 0;
}

int mpir_lexer_process_lexemme(char* lexeme, mpir_lexer* lexer)
{
    if (lexeme == NULL || strcmp(lexeme, "\0") == 0 || strcmp(lexeme, " ") == 0 || strlen(lexeme) == 0)
    {
        return 0;
    }
    else if (mpir_lexer_is_operator(lexeme))
    {
        printf("TOKEN_OPER\t\t%s\n", lexeme);
    }
    else if (mpir_lexer_is_keyword(lexeme))
    {
        printf("TOKEN_KW\t\t%s\n", lexeme);
    }
    else if (mpir_lexer_is_string_literal(lexeme))
    {
        printf("TOKEN_STRLIT\t%s\n", lexeme);
    }
    else if(mpir_lexer_has_newline(lexeme))
    {
        printf("TOKEN_EOL\t\t\\n\n");
    }
    else if(mpir_lexer_is_comment(lexeme))
    {
        printf("TOKEN_CMNT\t\t%s\n", lexeme);
    }
    else if(mpir_lexer_has_comma(lexeme))
    {
        printf("TOKEN_CMMA\t\t%s\n", lexeme);
    }
    else if(mpir_lexer_is_pipe(lexeme))
    {
        printf("TOKEN_PIPE\t\t%s\n", lexeme);
    }
    else if(mpir_lexer_is_colon(lexeme))
    {
        printf("TOKEN_COLN\t\t%s\n", lexeme);
    }
    else if(strcmp(lexeme, " ") != 0 && strcmp(lexeme, "\0") != 0)
    {
        printf("TOKEN_IDENT: \t%s\n", lexeme);
        mpir_token* tok = mpir_create_token(IDENTIFIER, lexeme, 0);
        mpir_lexer_append_token(lexer, tok);
    }

    return 0;
}