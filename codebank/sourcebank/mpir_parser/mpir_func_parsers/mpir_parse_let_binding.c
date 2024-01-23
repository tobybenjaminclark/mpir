/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../../headerbank/mpir_parser/mpir_func_parsers/mpir_parse_let_binding.h"

/**
 * @brief Function to parse a 'let' binding (type assignment) within the MPIR parser.
 *
 * This function parses a 'let' binding within the context of MPIR. A 'let' binding involves declaring a variable
 * with a specified type. The function sequentially parses the 'let' keyword, the variable identifier, the 'as' keyword,
 * and the associated type identifier. It then creates and returns a dynamically allocated `struct mpir_type_assignment`
 * representing the parsed 'let' binding as part of the AST.
 *
 * @param psr A pointer to the MPIR parser structure.
 *
 * @return A pointer to a dynamically allocated `struct mpir_type_assignment` on successful parsing.
 */
struct mpir_type_assignment* parse_let_binding(mpir_parser* psr, struct mpir_command_list* nodes)
{
    struct mpir_type_assignment* node = malloc(sizeof(struct mpir_type_assignment));

    /* Parse `let` */
    if(psr->peek(psr)->type == keyword_let) (void)psr->get(psr);
    else return NULL;

    /* Parse variable identifier */
    if(psr->peek(psr)->type == IDENTIFIER) wcscpy(node->identifier, (psr->get(psr))->lexeme);
    else return NULL;
    if(node->identifier == NULL) return NULL;

    /* Parse `as` */
    if(psr->peek(psr)->type == keyword_as) (void)psr->get(psr);
    else return NULL;

    /* Parse type identifier */
    if(psr->peek(psr)->type == IDENTIFIER) wcscpy(node->type, (psr->get(psr))->lexeme);
    else return NULL;
    if(node->type == NULL) return NULL;



    append_command(nodes, (union mpir_command_data){.type_assignment = node}, TYPE_ASSIGNMENT);

    return node;
}