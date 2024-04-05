/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../../headerbank/mpir_parser/mpir_func_parsers/mpir_parse_trycast.h"

/**
 * @brief Function to parse a 'trycast' statement within the MPiR parser.
 *
 * This expression parses a 'trycast' statement within the context of MPIR. The trycast statement attempts to cast a
 * variable of one type into a variable of another type. The expression parses the `trycast` keyword, followed by an
 * identifier, followed by the `into` keyword, followed by another identifier. It then creates & returns a dynamically
 * allocated `struct mpir_ast_trycast_statement` representing the parsed 'trycast' statement as part of the AST.
 *
 * @param psr A Pointer to the MPIR parser structure.
 * @param nodes A Pointer to a mpir_command_list structure (representing imperative statements in the AST)
 * @return Pointer to an allocate mpir_ast_trycast_statement struct or NULL on failure.
 */
struct mpir_ast_trycast_statement* parse_trycast(mpir_parser* psr, struct mpir_command_list* nodes)
{
    struct mpir_ast_trycast_statement* node = malloc(sizeof (struct mpir_ast_trycast_statement));

    /* Parse & Discard `Keyword` Variable */
    if(psr->peek(psr)->type == keyword_trycast) node->line_index = psr->get(psr)->line_index;
    else return NULL;

    printf("Parsed trycast keyword\n");

    /* Parse Dominant Variable */
    node->dominant_variable = parse_identifier(psr);
    if(node->dominant_variable == NULL) return NULL;

    printf("dominant trycast\n");

    /* Parse & Discard `into` keyword */
    if(psr->peek(psr)->type == keyword_into) (void)psr->get(psr);
    else return NULL;

    printf("into trycast\n");

    /* Parse 2nd Identifier (casted variable) */
    node->casted_variable = parse_identifier(psr);
    if(node->casted_variable == NULL) return NULL;

    printf("dominated trycast\n");

    /* Parse & discard newline. (if exists) */
    while (psr->peek(psr)->type == indentation) (void) psr->get(psr);
    if (psr->peek(psr)->type == NEWLINE) (void) psr->get(psr);
    while (psr->peek(psr)->type == indentation) (void) psr->get(psr);


    printf("newline trycast\n");

    /* Parse `on` statements */
    node->actions = PARSE_MULTIPLE_STATEMENTS(struct mpir_on_statement, parse_on_statement, psr);
    if(node->actions == NULL)
    {
        printf("on :: failed to parse multiple on statements for trycast\n");
        return NULL;
    }

    printf("parsed on statements successfully!\n");

    append_command(nodes, (union mpir_command_data){.trycast_statement = node}, TRYCAST_STATEMENT);
    return node;
}