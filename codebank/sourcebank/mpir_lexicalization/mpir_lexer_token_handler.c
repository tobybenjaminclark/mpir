
// GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark
// This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
// License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.

#include "../../headerbank/mpir_lexicalization/mpir_lexer_token_handler.h"

int mpir_lexer_has_newline(const char* lexeme) {
    // Iterate through the string
    for (int i = 0; lexeme[i] != '\0'; ++i)
    {
        // Check if the current character is a newline character
        if (lexeme[i] == '\n')
        {
            // If found, return 1 to indicate presence of newline character
            return 1;
        }
    }
    // If no newline character is found, return 0
    return 0;
}

int mpir_lexer_has_comma(const char* lexeme) {
    // Iterate through the string
    for (int i = 0; lexeme[i] != '\0'; ++i)
    {
        // Check if the current character is a newline character
        if (lexeme[i] == ',')
        {
            // If found, return 1 to indicate presence of newline character
            return 1;
        }
    }
    // If no newline character is found, return 0
    return 0;
}

int mpir_lexer_is_colon(char* lexeme)
{
    // Iterate through the string
    for (int i = 0; lexeme[i] != '\0'; ++i)
    {
        // Check if the current character is a newline character
        if (lexeme[i] == ':')
        {
            // If found, return 1 to indicate presence of newline character
            return 1;
        }
    }
    // If no newline character is found, return 0
    return 0;
}

int mpir_lexer_is_pipe(char* lexeme)
{
    // Iterate through the string
    for (int i = 0; lexeme[i] != '\0'; ++i)
    {
        // Check if the current character is a newline character
        if (lexeme[i] == '|')
        {
            // If found, return 1 to indicate presence of newline character
            return 1;
        }
    }
    // If no newline character is found, return 0
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
    // List of operators to check against
    const char* operators[] = {"+", "-", "*", "/", "%", "=="};
    int numOperators = sizeof(operators) / sizeof(operators[0]);

    for (int i = 0; i < numOperators; ++i)
    {
        if (strcmp(lexeme, operators[i]) == 0)
        {
            // If the input string matches any operator, return true
            return 1;
        }
    }

    // If no match found, return false
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
        if (first == last && (first == '"' || first == "'"))
        {
            return 1;
        }
    }
    return 0;
}

int mpir_lexer_process_lexemme(char* lexeme)
{
    //printf("Processing Lexeme [%s]\n", lexeme);
    if (lexeme == NULL || lexeme == "\0" || lexeme == " " || strlen(lexeme) == 0)
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
    else if(lexeme != " " || lexeme != "\0")
    {
        printf("TOKEN_IDENT: \t%s\n", lexeme);
    }

    return 0;
}