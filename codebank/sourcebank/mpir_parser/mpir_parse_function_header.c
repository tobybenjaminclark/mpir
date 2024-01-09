/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_parser/mpir_parse_function_header.h"

struct mpir_type** parse_inputs_internal(mpir_parser* psr, struct mpir_type** nodes, int node_index)
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
    nodes = realloc(nodes, sizeof(struct mpir_type*) * (node_index + 1));
    nodes[0] = parse_type(psr);

    if((psr->peek(psr))->type == keyword_comma)
    {
        /* The ',' token is voided, as it has no semantic integrity. */
        (void)psr->get(psr);
        node_index++;
        parse_inputs_internal(psr, nodes, node_index);
    }
    else if(psr->peek(psr)->type == operator_arrow)
    {
        /* No more types */
        return nodes;
    }
    else
    {
        mpir_error("Parser expected ', Type' or ->");
    }
}

struct mpir_type** parse_inputs(mpir_parser* psr)
{
    struct mpir_type** nodes;
    nodes = malloc(sizeof(struct mpir_type*));
    return parse_inputs_internal(psr, nodes, 0);
}

struct mpir_function_declaration* parse_function_declaration(mpir_parser* psr)
{
    /*
     * 'funcdef' identifier '::' function_io '\n'
     */

    /* Create Funcdef AST node & Consume 'fundef' */
    struct mpir_function_declaration node;
    /* Parsing */

    /* Parse `funcdef */
    if(psr->peek(psr)->type != keyword_funcdef) return NULL;
    else if(psr->peek(psr)->type == keyword_funcdef) (void)psr->get(psr);
    else return NULL;

    /* Parse function identifier */
    if(psr->peek(psr)->type == IDENTIFIER) node.identifier = node.identifier = parse_identifier(psr);
    else return NULL;
    if(node.identifier == NULL) return NULL;
    wprintf(L"Function Identifier: '%ls'\n", node.identifier);

    /* Parse I/O shield operator `::` */
    if(psr->peek(psr)->type != double_colon) return NULL;
    else if(psr->peek(psr)->type == double_colon) (void)psr->get(psr);
    else return NULL;
    printf("Parsed :: \n");

    /* Parse return type */
    if((node.inputs = parse_inputs(psr)) == NULL) return NULL;
    if(!(psr->tryget(psr, operator_arrow))) return NULL;
    if((node.return_type = parse_returntype(psr)) == NULL) return NULL;

    /* Parse Newline */
    if(psr->peek(psr)->type == NEWLINE) (void)psr->get(psr);
    else return NULL;

    /* Parse function body */
    node.body = parse_function_body(psr);

    /* Add Declaration Header to Program */
    add_declaration(psr->program, (union mpir_declaration_data){.function_declaration = &node});

    return psr;
}
