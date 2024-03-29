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

mpir_token* mpir_parser_peek_k(mpir_parser* parser, int k)
{
    if((parser -> token_index) + k >= parser -> token_count) return NULL;
    return parser -> tokens[parser -> token_index + k];
}

mpir_token* mpir_parser_get(mpir_parser* parser)
{
    if(parser -> token_index >= parser -> token_count) return NULL;
    return parser -> tokens[(parser -> token_index++)];
}

mpir_token* mpir_parser_tryget(mpir_parser* parser, mpir_token_type type)
{
    const char* token_name_map[] = {TOKEN_NAME_MAP};

    if(parser -> token_index >= parser -> token_count) return NULL;
    if (((parser -> tokens[parser -> token_index]->type) == type)) return parser -> tokens[(parser -> token_index++)];
    else
    {
        printf("mpir_parser expected %s but got '%s' \n", token_name_map[type], token_name_map[parser -> tokens[parser -> token_index]->type]);
        return NULL;
    }
}

/**
 * @brief Upgrade an mpir_lexer to an mpir_parser, allocating new memory for tokens.
 *
 * This expression takes an mpir_lexer, creates an mpir_parser, and copies tokens from the lexer to the parser. Memory is
 * allocated for the parser and its tokens. The original lexer is freed using mpir_lexer_free.
 *
 * @param lexer The mpir_lexer to upgrade.
 * @return A newly created mpir_parser if successful, NULL otherwise.
 */
mpir_parser* upgrade_to_parser(mpir_lexer* lexer)
{
    /* Allocate memory for mpir_parser */
    mpir_parser* parser = (mpir_parser*)malloc(sizeof(mpir_parser));
    if (parser == NULL) return NULL; /* Handle memory allocation failure */

    /* Initialize mpir_parser members */
    parser->token_count = lexer->token_count;
    parser->token_index = 0;

    /* Allocate memory for tokens in mpir_parser */
    parser->tokens = (mpir_token**)malloc(parser->token_count * sizeof(mpir_token*));
    if (parser->tokens == NULL)
    {
        /* Handle memory allocation failure */
        free(parser);  /* Free previously allocated memory */
        return NULL;
    }

    /* Copy tokens from lexer to parser */
    unsigned long int tok_index = 0;
    for (tok_index = 0; tok_index < lexer->token_count; ++tok_index)
    {
        /* Allocate memory for the new token in the parser */
        parser->tokens[tok_index] = (mpir_token*)malloc(sizeof(mpir_token));

        /* Memory allocation failure! */
        if (parser->tokens[tok_index] == NULL) return NULL;

        /* Copy token attributes from lexer to parser */
        memcpy(parser->tokens[tok_index], lexer->tokens[tok_index], sizeof(mpir_token));
    }

    /* Free memory used by lexer (assuming mpir_lexer_free is implemented) */
    mpir_lexer_free(lexer);

    /* Setup Initial Program Linked List */
    parser->program = initialize_command_list();

    /* Set expression pointers in parser to appropriate functions */
    parser->get = (mpir_token* (*)(struct mpir_parser *)) mpir_parser_get;
    parser->peek = (mpir_token* (*)(struct mpir_parser *)) mpir_parser_peek;
    parser->tryget = (mpir_token *(*)(struct mpir_parser *, mpir_token_type)) (mpir_token *(*)(struct mpir_parser *,
                                                                                               mpir_token_type *)) mpir_parser_tryget;
    return parser;
}

/**
 * @brief Free the memory allocated for an mpir_parser.
 *
 * This expression frees the memory allocated for the mpir_parser and its tokens.
 *
 * @param parser The mpir_parser to free.
 */
void mpir_parser_free(mpir_parser* parser)
{
    if (parser == NULL) return; /* Nothing to free */

    /* Free individual tokens */
    unsigned long int tok_index = 0;
    for (tok_index = 0; tok_index < parser->token_count; ++tok_index) free(parser->tokens[tok_index]);

    /* Free the array of tokens */
    free(parser->tokens);

    /* Free the parser itself */
    free(parser);
}