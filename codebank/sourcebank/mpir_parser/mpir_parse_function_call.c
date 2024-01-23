/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_parser/mpir_parse_function_call.h"

struct mpir_function_call* mpir_parse_function_call(mpir_parser* psr)
{
    /*  identifier `(` arg0 `,` arg1 `,` ... argn `)` */

    struct mpir_function_call* node = malloc(sizeof(struct mpir_function_call));

    /* Parse function identifier */
    if(psr->peek(psr)->type == IDENTIFIER) node->identifier = parse_function_identifier(psr);
    else return NULL;

    /* Parse `(` */
    if(psr->peek(psr)->type == open_bracket) (void)psr->get(psr);
    else return NULL;

    /* Parse Arguments */
    node->arguments = PARSE_MULTIPLE_STATEMENTS(struct mpir_expression, get_arg, psr);
    if(node->arguments == NULL) return NULL;

    int argument_count = 0;
    while (node->arguments[argument_count] != NULL) {
        wprintf(L"\t\t\t| Argument %d:\n", argument_count);
        mpir_display_ast(node->arguments[argument_count], 0);
        argument_count++;
    }

    /* Parse `\n` */
    if(psr->peek(psr)->type == NEWLINE) (void)psr->get(psr);
    else return NULL;

    return node;
}