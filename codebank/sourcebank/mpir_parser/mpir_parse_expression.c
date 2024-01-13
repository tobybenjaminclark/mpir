/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_parser/mpir_parse_expression.h"

struct mpir_expression* mpir_parse_expression(mpir_parser* psr)
{
    return NULL;
}

struct mpir_identifier* get_arg(mpir_parser* psr)
{
    if(psr->peek(psr)->type != IDENTIFIER) return NULL;

    struct mpir_identifier* arg = malloc(sizeof (struct mpir_identifier));
    wcscpy(arg->data, psr->get(psr)->lexeme);
    if(psr->peek(psr)->type == keyword_comma) (void)psr->get(psr);
    return arg;
}


struct mpir_identifier** parse_arguments(mpir_parser* psr)
{
    struct mpir_identifier** nodes = NULL;

    int arg_index = 0;
    struct mpir_identifier* arg;
    while((arg = get_arg(psr)) != NULL)
    {
        // Reallocate memory and assign the result back to nodes
        struct mpir_identifier** temp = realloc(nodes, (arg_index + 1) * sizeof(struct mpir_identifier*));
        if (temp == NULL)
        {
            free(nodes);
            return NULL;
        }
        nodes = temp;

        nodes[arg_index] = arg;
        arg_index++;
    }

    // Ensure the array is properly terminated with NULL
    nodes[arg_index] = NULL;
    return nodes;
}


struct mpir_function_call* mpir_parse_function_call(mpir_parser* psr)
{
    /*  identifier `(` arg0 `,` arg1 `,` ... argn `)` */

    struct mpir_function_call node;

    /* Parse function identifier */
    if(psr->peek(psr)->type == IDENTIFIER) node.identifier = parse_function_identifier(psr);
    else return NULL;

    /* Parse `(` */
    if(psr->peek(psr)->type == open_bracket) (void)psr->get(psr);
    else return NULL;

    /* Parse Arguments */
    node.arguments = parse_arguments(psr);
    if(node.arguments == NULL) return NULL;

    wprintf(L"\tFunction Call to `%ls` with args: \n", node.identifier->data);
    int argument_count = 0;
    while (node.arguments[argument_count] != NULL) {
        wprintf(L"\t\tArgument %d: %ls\n", argument_count, node.arguments[argument_count]->data);
        argument_count++;
    }

    /* Parse `)` */
    if(psr->peek(psr)->type == close_bracket) (void)psr->get(psr);
    else return NULL;

    return &node;
}
