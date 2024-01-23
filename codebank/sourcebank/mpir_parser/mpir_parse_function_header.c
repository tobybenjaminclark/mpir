/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_parser/mpir_parse_function_header.h"

struct mpir_type* get_type(mpir_parser* psr)
{
    if(psr->peek(psr)->type != IDENTIFIER) return NULL;

    struct mpir_type* arg = calloc(1, sizeof (struct mpir_identifier));
    wcscpy(arg->data, psr->get(psr)->lexeme);
    if(psr->peek(psr)->type == keyword_comma) (void)psr->get(psr);
    return arg;
}

struct mpir_type** parse_inputs(mpir_parser* psr)
{
    struct mpir_identifier** nodes = NULL;

    int arg_index = 0;
    struct mpir_identifier* arg;
    while((arg = get_type(psr)) != NULL)
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

/**
 * @brief Function to parse a Function Header, returns a mpir_function_declaration structure.
 *
 * This function is responsible for parsing the declaration of a function according to the MPIR Grammar. It gathers
 * the identifier, input types, and output types. Performs memory allocation for the list of input types. The decl.
 * is added to the declaration list in the parser. The grammar can be seen below, and also in the CFG documentation.
 * `funcdef' identifier '::' function_io '\n'`
 *
 * @param psr A pointer to the MPIR parser structure.
 * @return True on parsing success, False on parsing failure.
 */
bool parse_function_declaration(mpir_parser* psr)
{
    /* Create Funcdef AST node & Consume 'fundef' */
    struct mpir_function_declaration* node = calloc(1, sizeof(struct mpir_function_declaration));
    /* Parsing */

    /* Parse `funcdef */
    if(psr->peek(psr)->type != keyword_funcdef) return false;
    else if(psr->peek(psr)->type == keyword_funcdef) (void)psr->get(psr);
    else return false;

    /* Parse function identifier */
    if(psr->peek(psr)->type == IDENTIFIER) node->identifier = parse_identifier(psr);
    else return false;
    if(node->identifier == NULL) return false;

    /* Parse I/O shield operator `::` */
    if(psr->peek(psr)->type != double_colon) return false;
    else if(psr->peek(psr)->type == double_colon) (void)psr->get(psr);
    else return false;

    /* Parse return type */
    if((node->inputs = PARSE_MULTIPLE_STATEMENTS(struct mpir_type , get_type, psr)) == NULL) return false;
    if(!(psr->tryget(psr, operator_arrow))) return false;
    if((node->return_type = parse_returntype(psr)) == NULL) return false;

    /* Parse Newline */
    if(psr->peek(psr)->type == NEWLINE) (void)psr->get(psr);
    else return false;

    /* Parse function body */
    node->body = parse_function_body(psr);

    /* Add Declaration Header to Program & Return PSR*/
    append_command(psr->program, (union mpir_command_data){.function_declaration = node}, FUNCTION_DECLARATION);

    return true;
}
