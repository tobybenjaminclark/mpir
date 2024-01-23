/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../../headerbank/mpir_parser/mpir_func_parsers/mpir_parse_trycast.h"

struct mpir_trycast_statement* parse_trycast(mpir_parser* psr, struct mpir_command_list* nodes)
{
    struct mpir_trycast_statement* node = malloc(sizeof (struct mpir_trycast_statement));
    printf("Parsing Trycast!\n");

    /* Parse & Discard `Keyword` Variable */
    if(psr->peek(psr)->type == keyword_trycast) (void)psr->get(psr);
    else return NULL;
    printf("Parsing Trycast!\n");

    /* Parse Dominant Variable */
    node->dominant_variable = parse_identifier(psr);
    if(node->dominant_variable == NULL) return NULL;
    wprintf(L"Parsing Trycast! Dominant Variable -> %ls\n", node->dominant_variable->data);

    /* Parse & Discard `into` keyword */
    if(psr->peek(psr)->type == keyword_into) (void)psr->get(psr);
    else return NULL;
    printf("Parsing Trycast!\n");

    /* Parse 2nd Identifier (casted variable) */
    node->casted_variable = parse_identifier(psr);
    if(node->casted_variable == NULL) return NULL;
    wprintf(L"Parsing Trycast! Casted Variable -> %ls\n", node->casted_variable->data);

    /* Parse `\n` */
    if(psr->peek(psr)->type == NEWLINE) (void)psr->get(psr);
    else return NULL;
    printf("Parsing Trycast!\n");

    /* Parse `on` statements */
    node->actions = PARSE_MULTIPLE_STATEMENTS(struct mpir_on_statement, parse_on_statement, psr);
    //  PARSE_MULTIPLE_STATEMENTS(struct mpir_on_statement, parse_on_statement, psr);
    if(node->actions == NULL) return NULL;
    printf("Parsing Trycast!\n");

    append_command(nodes, (union mpir_command_data){.trycast_statement = node}, TRYCAST_STATEMENT);
    return node;
}