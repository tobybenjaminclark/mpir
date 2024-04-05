/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../../headerbank/mpir_parser/mpir_func_parsers/mpir_parse_do.h"

/**
 * @brief Parses a do statement within the MPIR parser.
 *
 * This expression parses a `do` statement from the provided MPIR parser, including the associated expression call
 * and the following list of `on` statements. It creates, allocates and returns a `mpir_ast_do_statement` structure,
 * which gets returned. The statement is parsed in accoradance with the MPIR grammar.
 *
 * @param psr Pointer to the parser structure.
 * @param nodes Pointer to the command list to which the parsed `do` statement will be appended.
 *
 * @return A pointer to a dynamically allocated `mpir_ast_do_statement` structure representing the parsed `do` statement.
 *         Returns NULL if the parsing fails or encounters an unexpected structure.
 */
struct mpir_ast_do_statement* parse_do(mpir_parser* psr, struct mpir_command_list* nodes)
{
    /* Fetch & Disregard Indentation */
    while (psr->peek(psr)->type == indentation) (void) psr->get(psr);

    /* Parse & discard `do` keyword. */
    if (psr->peek(psr)->type == keyword_do) (void) psr->get(psr);
    else return NULL;

    /* Allocate Memory for Do Node */
    struct mpir_ast_do_statement *node = malloc(sizeof(struct mpir_ast_do_statement));
    node->line_index = psr->peek(psr)->line_index;

    /* Try to parse expression */
    node->expression = mpir_parse_expression(psr, indentation, 0);
    if(node->expression == NULL) return NULL;

    /* Parse & discard newline. (if exists) */
    while (psr->peek(psr)->type == indentation) (void) psr->get(psr);
    if (psr->peek(psr)->type == NEWLINE) (void) psr->get(psr);
    while (psr->peek(psr)->type == indentation) (void) psr->get(psr);


    /* Parse on statements */
    node->actions = PARSE_MULTIPLE_STATEMENTS(struct mpir_on_statement, parse_on_statement, psr);
    if(node->actions == NULL) return NULL;

    /* Append the command to the command list & return the node pointer */
    append_command(nodes, (union mpir_command_data){.do_statement = node}, DO_STATEMENT);
    return node;
}
