/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_parser/mpir_parser.h"


mpir_token* mpir_parser_peek(mpir_parser* parser)
{
    if(parser -> token_index >= parser -> token_count) return NULL;
    return parser -> tokens[parser -> token_index];
}

mpir_token* mpir_parser_get(mpir_parser* parser)
{
    if(parser -> token_index >= parser -> token_count) return NULL;
    return parser -> tokens[(parser -> token_index++)];
}

mpir_parser* create_parser(mpir_lexer* lexer)
{
    mpir_parser* parser = malloc(sizeof(mpir_parser));
    printf("I");
    if(lexer->tokens == NULL)
    {
        mpir_fatal("mpir_parser: failed to create parser, token array is null.");
        return 0;
    }
    parser->tokens = malloc(sizeof(mpir_token) * (sizeof(lexer->tokens))/(sizeof(lexer->tokens[0])));
    parser->tokens = lexer->tokens;
    parser->token_count = (unsigned long int) (sizeof(parser->tokens) / sizeof(parser->tokens[0]));
    parser->token_index = 0;
    parser->get = (mpir_token* (*)(struct mpir_parser *)) mpir_parser_get;
    parser->peek = (mpir_token* (*)(struct mpir_parser *)) mpir_parser_peek;
    return parser;
}

void mpir_parse(mpir_parser* parser)
{
    mpir_token* current_token = parser->get(parser);
    while(current_token != NULL)
    {
        wprintf(L"%ls\n", current_token->lexeme);
        current_token = parser->get(parser);
    }
    return;
}

void parse_function_declaration(mpir_token** list_of_tokens)
{
    /*
     * 'funcdef' identifier '::' function_io '\n'
     */

}