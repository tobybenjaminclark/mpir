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

/**
 * @brief Function to parse a Function Header, returns a mpir_function_declaration structure.
 *
 * This function is responsible for parsing the declaration of a function according to the MPIR Grammar. It gathers
 * the identifier, input types, and output types. Performs memory allocation for the list of input types. The decl.
 * is added to the declaration list in the parser. The grammar can be seen below, and also in the CFG documentation.
 * `funcdef' identifier '::' function_io '\n'`
 *
 * @param psr A pointer to the MPiR parser structure.
 * @return True on parsing success, False on parsing failure.
 */
bool parse_function_declaration(mpir_parser* psr)
{
    /* Create Funcdef AST node & Consume 'fundef' */
    struct mpir_function_declaration node;
    /* Parsing */

    /* Parse `funcdef */
    if(psr->peek(psr)->type != keyword_funcdef) return false;
    else if(psr->peek(psr)->type == keyword_funcdef) (void)psr->get(psr);
    else return false;

    /* Parse function identifier */
    if(psr->peek(psr)->type == IDENTIFIER) node.identifier = node.identifier = parse_identifier(psr);
    else return false;
    if(node.identifier == NULL) return false;
    wprintf(L"Function Identifier: '%ls'\n", node.identifier);

    /* Parse I/O shield operator `::` */
    if(psr->peek(psr)->type != double_colon) return false;
    else if(psr->peek(psr)->type == double_colon) (void)psr->get(psr);
    else return false;
    printf("Parsed :: \n");

    /* Parse return type */
    if((node.inputs = parse_inputs(psr)) == NULL) return false;
    if(!(psr->tryget(psr, operator_arrow))) return false;
    if((node.return_type = parse_returntype(psr)) == NULL) return false;

    /* Parse Newline */
    if(psr->peek(psr)->type == NEWLINE) (void)psr->get(psr);
    else return false;

    /* Parse function body */
    node.body = parse_function_body(psr);

    /* Add Declaration Header to Program & Return PSR*/
    add_declaration(psr->program, (union mpir_declaration_data){.function_declaration = &node});
    return true;
}
