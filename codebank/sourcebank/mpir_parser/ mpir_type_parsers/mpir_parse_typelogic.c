/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../../headerbank/mpir_parser/mpir_type_parsers/mpir_parse_typelogic.h"

mpir_token_type PRESEDENCE_TABLE[] = {
        operator_and,
        operator_or,
        operator_eq,
        operator_lteq,
        operator_lt,
        operator_gt,
        operator_gteq
};

void internal_parse_type_logic(struct boolean_logic_token** node_ptr, int presedence)
{
    /* Used as a counter */
    unsigned long int i;
    int delimiter_found = 0;

    if(presedence < 0 || presedence > 6) return;

    mpir_token_type delimiter = PRESEDENCE_TABLE[presedence];
    struct boolean_logic_token* node = *node_ptr;

    /* Node is singular and cannot be broken down further */
    if(node->token_count == 1) return;

    /* Check if the delimiter is present in the list */
    for (i = 0; i < node->token_count; i++)
    {
        if (node->tokens[i]->type == delimiter)
        {
            delimiter_found = 1;
            break;
        }
    }

    if (!delimiter_found)
    {
        /* If delimiter is not present, print the original list */
        internal_parse_type_logic(node_ptr, ++presedence);
        return;
    }

    /* Split the list into three based on the delimiter */
    struct boolean_logic_token* left_tokens = malloc(sizeof(struct boolean_logic_token));
    struct boolean_logic_token* central_tokens = malloc(sizeof(struct boolean_logic_token));
    struct boolean_logic_token* right_tokens = malloc(sizeof(struct boolean_logic_token));

    left_tokens->token_count = 0;
    central_tokens->token_count = 0;
    right_tokens ->token_count = 0;

    left_tokens->tokens = (mpir_token**)malloc(node->token_count * sizeof(mpir_token*));
    central_tokens->tokens = (mpir_token**)malloc(node->token_count * sizeof(mpir_token*));
    right_tokens->tokens = (mpir_token**)malloc(node->token_count * sizeof(mpir_token*));

    for (i = 0; i < node->token_count; i++) {
        /* If it isn't the delimiter */
        if (node->tokens[i]->type != delimiter) {
            left_tokens->tokens[left_tokens->token_count++] = node->tokens[i];
        } else {
            /* If it is the delimiter */
            central_tokens->tokens[central_tokens->token_count++] = node->tokens[i];
            break;
        }
    }

    /* Copy the remaining tokens to right_tokens */
    right_tokens->tokens = (mpir_token**)malloc((node->token_count - left_tokens->token_count - 1) * sizeof(mpir_token*));
    for (i = left_tokens->token_count + 1; i < node->token_count; i++) {
        right_tokens->tokens[i - left_tokens->token_count - 1] = node->tokens[i];
        right_tokens->token_count++;
    }

    /* Readjust pointers */
    free(node->tokens);
    free(node);

    central_tokens->left = left_tokens;
    central_tokens->right = right_tokens;
    *node_ptr = central_tokens;

    // Print the token lexemes of left_tokens, central_tokens, and right_tokens
    printf("Left: [");
    for (i = 0; i < central_tokens->left->token_count; i++) {
        wprintf(L"%ls ", central_tokens->left->tokens[i]->lexeme);
    }
    printf("]\n");

    printf("Middle: [");
    for (i = 0; i < central_tokens->token_count; i++) {
        wprintf(L"%ls ", central_tokens->tokens[i]->lexeme);
    }
    printf("]\n");

    printf("Right: [");
    for (i = 0; i < central_tokens->right->token_count; i++) {
        wprintf(L"%ls ", central_tokens->right->tokens[i]->lexeme);
    }
    printf("]\n");

    // Update the node_ptr content
    *node_ptr = central_tokens;

    // Recursively call parse_type_logic on the left and right
    internal_parse_type_logic(&(central_tokens->left), presedence);
    internal_parse_type_logic(&(central_tokens->right), presedence);


    return;
}

enum type_logic_operator get_ast_logic_mapping(mpir_token_type tok_type)
{
    /* Get Value */
    switch(tok_type)
    {
        case operator_eq: return EQ;
        case operator_lt: return LT;
        case operator_lteq: return LTEQ;
        case operator_gt: return GT;
        case operator_gteq: return GTEQ;
        case operator_and: return AND;
        case operator_or: return OR;
    }
}

struct type_logic* convert_to_type_logic(struct boolean_logic_token* node_ptr)
{
    struct type_logic* node = calloc(1, sizeof(struct type_logic));
    mpir_token_type tok_type = node_ptr->tokens[0]->type;



    /* Recursive Call if not NULL */

    return NULL;
}

struct mpir_type_logic* parse_type_logic(mpir_parser* psr)
{
    /* Parse & discard '{' */
    if(psr->peek(psr)->type == open_brace) (void)psr->get(psr);
    else return NULL;

    mpir_token** tokens = malloc(sizeof(struct mpir_token*));

    /* Allocate memory for tokens */;
    if (tokens == NULL) return NULL;

    /* Copy tokens from lexer */
    unsigned long int tok_index = 0;
    while(psr->peek(psr)->type != close_brace && psr->peek(psr)->type != WEOF)
    {
        /* Allocate memory for the new token in the parser */
        tokens = realloc(tokens, (tok_index + 1) * sizeof(struct mpir_token*));
        tokens[tok_index] = psr->get(psr);
        tok_index++;
    }

    struct boolean_logic_token* root = malloc(sizeof(struct boolean_logic_token));
    root->tokens = tokens;
    root->left = NULL;
    root->right = NULL;
    root->token_count = tok_index;

    if(psr->peek(psr)->type == close_brace) (void)psr->get(psr);
    else return NULL;

    internal_parse_type_logic(&root, 0);

    return NULL;
}