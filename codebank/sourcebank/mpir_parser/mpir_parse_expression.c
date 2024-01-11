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

struct mpir_identifier** parse_arguments_internal(mpir_parser* psr, struct mpir_identifier** nodes, int node_index)
{
    /*
     * Needs to dynamically read & process types i.e. Int, Int or Int, Float,
     */

    if((psr->peek(psr))->type != IDENTIFIER)
    {
        mpir_error("parse_function_declaration: expected function identifier got other.");
        return NULL;
    }

    /* Allocate Memory for list of types */
    nodes = realloc(nodes, sizeof(struct mpir_identifier*) * (node_index + 1));
    nodes[0] = parse_type(psr);

    if((psr->peek(psr))->type == keyword_comma)
    {
        /* The ',' token is voided, as it has no semantic integrity. */
        (void)psr->get(psr);
        node_index++;
        parse_arguments_internal(psr, nodes, node_index);
    }
    else if(psr->peek(psr)->type == close_bracket)
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
    struct mpir_type** nodes;
    nodes = malloc(sizeof(struct mpir_identifier*));
    return parse_arguments_internal(psr, nodes, 0);
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

    wprintf(L"Parsed: Function call to %ls \n", (node.identifier->data));

    return &node;
}
