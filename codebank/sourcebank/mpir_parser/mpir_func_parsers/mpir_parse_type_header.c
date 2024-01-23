/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../../headerbank/mpir_parser/mpir_func_parsers/mpir_parse_type_header.h"

struct mpir_identifier* get_type_arg(mpir_parser* psr)
{
    if(psr->peek(psr)->type != IDENTIFIER) return NULL;

    struct mpir_identifier* arg = calloc(1, sizeof (struct mpir_identifier));
    wcscpy(arg->data, psr->get(psr)->lexeme);
    if(psr->peek(psr)->type == keyword_comma) (void)psr->get(psr);
    return arg;
}

struct mpir_identifier** parse_type_args(mpir_parser* psr)
{
    struct mpir_identifier** nodes = NULL;

    int arg_index = 0;
    struct mpir_identifier* arg;
    while((arg = get_type_arg(psr)) != NULL)
    {
        struct mpir_identifier** temp = realloc(nodes, (arg_index + 2) * sizeof(struct mpir_identifier*));
        if (temp == NULL)
        {
            free(nodes);
            return NULL;
        }
        nodes = temp;

        nodes[arg_index] = arg;
        arg_index++;
    }

    nodes[arg_index] = NULL;
    return nodes;
}

bool parse_type_header(mpir_parser* psr)
{
    /* Create Funcdef AST node & Consume 'fundef' */
    struct mpir_type_declaration node;
    /* Parsing */

    /* Parse `funcdef */
    if(psr->peek(psr)->type != keyword_typedef) return false;
    else if(psr->peek(psr)->type == keyword_typedef) (void)psr->get(psr);
    else return false;

    /* Parse function identifier */
    if(psr->peek(psr)->type == IDENTIFIER) node.identifier = node.identifier = parse_identifier(psr);
    else return false;
    if(node.identifier == NULL) return false;
    wprintf(L"Function Identifier: '%ls'\n", node.identifier);

    /* Parse return type */
    if((node.inputs = parse_type_args(psr)) == NULL) return false;

    /* Parse I/O shield operator `::` */
    if(psr->peek(psr)->type != double_colon) return false;
    else if(psr->peek(psr)->type == double_colon) (void)psr->get(psr);
    else return false;

    if((node.base_type = parse_returntype(psr)) == NULL) return false;

    /* Parse Newline */
    if(psr->peek(psr)->type == NEWLINE) (void)psr->get(psr);
    else return false;

    /* Add Declaration Header to Program & Return PSR*/
    append_command(psr->program, (union mpir_command_data){.type_declaration = &node}, TYPE_DECLARATION);

    return true;
}