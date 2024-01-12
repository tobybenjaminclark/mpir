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

/*
 * TODO: fix argument parsing
 * */
struct mpir_identifier** parse_arguments_internal(mpir_parser* psr, struct mpir_identifier** nodes, int node_index)
{
    if ((psr->peek(psr))->type != IDENTIFIER)
    {
        mpir_error("parse_function_declaration: expected function identifier got other.");
        return NULL;
    }

    /* Allocate Memory for list of types */
    nodes = realloc(nodes, sizeof(struct mpir_identifier*) * (node_index + 1));
    nodes[node_index] = parse_identifier(psr);

    wprintf(L"Argument Identifier %ls inserted at index %d\n", nodes[node_index]->data, node_index);

    if ((psr->peek(psr))->type == keyword_comma)
    {
        /* The ',' token is voided, as it has no semantic integrity. */
        (void)psr->get(psr);
        parse_arguments_internal(psr, nodes, node_index++);  // Fix: Update node_index
    }
    else if (psr->peek(psr)->type == close_bracket)
    {
        /* No more types */
        return nodes;
    }
    else
    {
        mpir_error("Parser expected ', Type' or ->");
    }
}

struct mpir_identifier** parse_arguments(mpir_parser* psr)
{
    struct mpir_identifier** nodes = malloc(sizeof(struct mpir_identifier*));
    nodes = parse_arguments_internal(psr, nodes, 0);

    printf("Showing parameters:\n");
    int argument_count = sizeof(nodes) / sizeof(nodes[0]);
    printf("Total of %d arguments. size: %d \n", argument_count, sizeof(nodes));
    int argument_index;

    for (argument_index = 0; argument_index < argument_count; argument_index++)
    {
        wprintf(L"%ls\n", nodes[argument_index]->data);

        if (argument_index < argument_count - 1)
        {
            wprintf(L", ");
        }
    }
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

    /* Parse `)` */
    if(psr->peek(psr)->type == close_bracket) (void)psr->get(psr);
    else return NULL;

    wprintf(L"Parsed: Function call to %ls with arguments: [", (node.identifier->data));
    int argument_count = sizeof(node.arguments) / sizeof(node.arguments[0]);
    int argument_index;

    for (argument_index = 0; argument_index < argument_count; argument_index++)
    {
        wprintf(L"%ls ", node.arguments[argument_index]->data);

        if (argument_index < argument_count - 1)
        {
            wprintf(L", ");
        }
    }

    wprintf(L"].\n");
    return &node;
}
