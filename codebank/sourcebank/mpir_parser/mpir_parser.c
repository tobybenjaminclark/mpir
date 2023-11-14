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



void mpir_parser_free(mpir_parser* parser)
{
    if (parser == NULL) {
        return; // Nothing to free
    }

    // Free individual tokens
    for (unsigned long int i = 0; i < parser->token_count; ++i) {
        free(parser->tokens[i]);
    }

    // Free the array of tokens
    free(parser->tokens);

    // Free the parser itself
    free(parser);
}



/* Function to upgrade mpir_lexer to mpir_parser */
mpir_parser* upgrade_to_parser(mpir_lexer* lexer)
{
    // Allocate memory for mpir_parser
    mpir_parser* parser = (mpir_parser*)malloc(sizeof(mpir_parser));
    if (parser == NULL) {
        // Handle memory allocation failure
        return NULL;
    }

    // Initialize mpir_parser members
    parser->token_count = lexer->token_count;
    parser->token_index = 0;

    // Allocate memory for tokens in mpir_parser
    parser->tokens = (mpir_token**)malloc(parser->token_count * sizeof(mpir_token*));
    if (parser->tokens == NULL) {
        // Handle memory allocation failure
        free(parser);  // Free previously allocated memory
        return NULL;
    }

    // Copy tokens from lexer to parser
    for (unsigned long int i = 0; i < lexer->token_count; ++i)
    {
        // Allocate memory for the new token in the parser
        parser->tokens[i] = (mpir_token*)malloc(sizeof(mpir_token));
        if (parser->tokens[i] == NULL)
        {
            // Handle memory allocation failure
            // You may need to free previously allocated memory before returning
            return NULL;
        }

        // Copy token attributes from lexer to parser
        memcpy(parser->tokens[i], lexer->tokens[i], sizeof(mpir_token));
    }

    // Free memory used by lexer (assuming mpir_lexer_free is implemented)
    mpir_lexer_free(lexer);

    // Set function pointers in parser to appropriate functions
    parser->get = (mpir_token* (*)(struct mpir_parser *)) mpir_parser_get;
    parser->peek = (mpir_token* (*)(struct mpir_parser *)) mpir_parser_peek;

    return parser;
}

void mpir_parse(mpir_parser* parser)
{
    mpir_token* current_token = parser->get(parser);
    while(current_token != NULL)
    {
        wprintf(L"Token is '%ls'\n", current_token->lexeme);
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