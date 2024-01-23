/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../../headerbank/mpir_parser/mpir_parsers/mpir_parse_do.h"

struct mpir_do_statement* parse_do(mpir_parser* psr, struct mpir_command_list* nodes) {
    struct mpir_do_statement *node = malloc(sizeof(struct mpir_do_statement));

    /* Fetch & Disregard Indentation */
    while (psr->peek(psr)->type == indentation) (void) psr->get(psr);

    /* Parse & discard `do` keyword. */
    if (psr->peek(psr)->type == keyword_do) (void) psr->get(psr);
    else return NULL;
    printf("Parsed `DO`!\n");

    /* Try to parse function call */
    if ((node->function = mpir_parse_function_call(psr)) == NULL) return NULL;
    printf("Parsed func call!\n");

    /* Parse & discard newline. (if exists) */
    if (psr->peek(psr)->type == NEWLINE) (void) psr->get(psr);

    /* Parse on statements */
    wprintf(L"\n\n\nNEXT TOKEN LEXEME is %ls \n", psr->peek(psr)->lexeme);
    node->actions = PARSE_MULTIPLE_STATEMENTS(struct mpir_on_statement, parse_on_statement, psr);

    printf("a");

    if(node->actions == NULL) return NULL;

    append_command(nodes, (union mpir_command_data){.do_statement = node}, DO_STATEMENT);
    return node;
}
