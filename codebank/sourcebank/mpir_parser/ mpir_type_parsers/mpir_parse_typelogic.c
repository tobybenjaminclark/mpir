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

void parse_and(struct boolean_logic_token** node_ptr, int presedence)
{
    /* Used as a counter */
    unsigned long int i;
    int delimiter_found = 0;

    if(presedence < 0 || presedence > 6) return;

    mpir_token_type delimiter = PRESEDENCE_TABLE[presedence];
    struct boolean_logic_token* node = *node_ptr;


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
        printf("%d\n", presedence);
        parse_and(node_ptr, ++presedence);
        return;
    }

    /* Split the list into three based on the delimiter */
    struct boolean_logic_token* list1 = malloc(sizeof(struct boolean_logic_token));
    struct boolean_logic_token* list2 = malloc(sizeof(struct boolean_logic_token));
    struct boolean_logic_token* list3 = malloc(sizeof(struct boolean_logic_token));

    list1->token_count = 0;
    list2->token_count = 0;
    list3->token_count = 0;

    list1->tokens = (mpir_token**)malloc(node->token_count * sizeof(mpir_token*));
    list2->tokens = (mpir_token**)malloc(node->token_count * sizeof(mpir_token*));
    list3->tokens = (mpir_token**)malloc(node->token_count * sizeof(mpir_token*));

    for (i = 0; i < node->token_count; i++) {
        /* If it isn't the delimiter */
        if (node->tokens[i]->type != delimiter) {
            list1->tokens[list1->token_count++] = node->tokens[i];
        } else {
            /* If it is the delimiter */
            list2->tokens[list2->token_count++] = node->tokens[i];
            break;
        }
    }

    /* Copy the remaining tokens to list3 */
    list3->tokens = (mpir_token**)malloc((node->token_count - list1->token_count - 1) * sizeof(mpir_token*));
    for (i = list1->token_count + 1; i < node->token_count; i++) {
        list3->tokens[i - list1->token_count - 1] = node->tokens[i];
        list3->token_count++;
    }

    /* Readjust pointers */
    free(node->tokens);
    free(node);

    list2->left = list1;
    list2->right = list3;
    *node_ptr = list2;

    // Print the token lexemes of list1, list2, and list3
    printf("List 1: [");
    for (i = 0; i < list2->left->token_count; i++) {
        wprintf(L"%ls ", list2->left->tokens[i]->lexeme);
    }
    printf("]\n");

    printf("List 2: [");
    for (i = 0; i < list2->token_count; i++) {
        wprintf(L"%ls ", list2->tokens[i]->lexeme);
    }
    printf("]\n");

    printf("List 3: [");
    for (i = 0; i < list2->right->token_count; i++) {
        wprintf(L"%ls ", list2->right->tokens[i]->lexeme);
    }
    printf("]\n");

    // Update the node_ptr content
    *node_ptr = list2;

    // Recursively call parse_and on the left and right
    parse_and(&(list2->left), presedence);
    parse_and(&(list2->right), presedence);


    return;
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

    parse_and(&root, 0);

    return NULL;
}