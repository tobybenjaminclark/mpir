/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../../headerbank/mpir_parser/mpir_types_parsers/mpir_parse_typedef.h"

bool parse_type_declaration(mpir_parser* psr)
{
    /* Attempt to Parse * Discard 'typedef' keyword */
    if(psr->peek(psr)->type == keyword_typedef) (void)psr->get(psr);
    else return false;

    /* Allocate Memory for type declaration AST node */
    struct mpir_ast_type_declaration* node = calloc(1, sizeof(struct mpir_ast_type_declaration));

    /* Attempt to Parse Type Identifier */
    if(psr->peek(psr)->type == IDENTIFIER) node->identifier = parse_identifier(psr);
    else return false;

    /* Attempt to Parse Inputs */
    if((node->inputs = PARSE_MULTIPLE_STATEMENTS(struct mpir_type , get_type, psr)) == NULL) return false;

    /* Attempt to Parse Double Colon */
    if(psr->peek(psr)->type == double_colon) (void)psr->get(psr);
    else return false;

    /* Parse Base Type */
    if(psr->peek(psr)->type == IDENTIFIER || psr->peek(psr)->type == open_sqbracket) node->base_type = parse_returntype(psr);
    else
    {
        wprintf(L"Couldn't parse returntype for %ls \n", node->identifier);
        return false;
    }

    /* Parse Type Logic */
    node->refinement = parse_type_logic(psr);

    printf("Going to try and docsection for type declaration!\n");
    if(psr->peek(psr)->type == NEWLINE) (void)psr->get(psr);

    /* Parse Doc */
    if(psr->peek(psr)->type == keyword_suchthat)
    {
        /* Consume Suchthat */
        (void)psr->get(psr);
        if(psr->peek(psr)->type == colon) (void)psr->get(psr);
        else
        {
            printf("Expected :");
            return NULL;
        }
        printf("Parsing docsection for type declaration!\n");
        node -> docsection = mpir_parse_docsection(psr);
    }
    else if(psr->peek(psr)->type == keyword_end)
    {
        printf("See END!");
        (void)psr->get(psr);
        node -> docsection = NULL;
        printf("Failed Parsing docsection for type declaration!\n");
    }
    else
    {
        wprintf(L"Expected Suchthat, got %ls \n", psr->peek(psr)->lexeme);
    }
    append_command(psr->program, (union mpir_command_data){.type_declaration = node}, NEW_TYPE_DECLARATION);

    printf("Found docs!\n");
    return true;
}