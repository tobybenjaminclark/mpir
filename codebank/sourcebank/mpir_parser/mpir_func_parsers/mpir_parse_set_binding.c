/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../../headerbank/mpir_parser/mpir_func_parsers/mpir_parse_set_binding.h"

/**
 * @brief Function to parse a 'set' binding (value assignment) within the MPIR parser.
 *
 * This function parses a 'set' binding within the context of the MPIR. A 'set' binding involves assigning a value to a
 * variable with a specified type. The function sequentially parses the 'set' keyword, the variable identifier, the 'as'
 * keyword, and the associated expression (value). It then creates and returns a dynamically allocated
 * `struct mpir_value_assignment` representing the parsed 'set' binding.
 *
 * @param psr A pointer to the MPIR parser structure.
 * @return A pointer to a dynamically allocated `struct mpir_value_assignment` on successful parsing.
 */
struct mpir_value_assignment* parse_set_binding(mpir_parser* psr, struct mpir_command_list* nodes)
{
    struct mpir_value_assignment* node = calloc(1, sizeof(struct mpir_value_assignment));

    /* Parse `set` */
    if(psr->peek(psr)->type == keyword_set) (void)psr->get(psr);
    else return NULL;

    /* Parse variable identifier */
    if(psr->peek(psr)->type == IDENTIFIER) wcscpy(node->identifier, (psr->get(psr))->lexeme);
    else return NULL;
    if(node->identifier == NULL) return NULL;

    /* Parse `as` */
    if(psr->peek(psr)->type == keyword_as) (void)psr->get(psr);
    else return NULL;

    /* Parse expression */
    node->expression = mpir_parse_expression(psr, NEWLINE, 0);
    mpir_display_ast(node->expression, 0);

    append_command(nodes, (union mpir_command_data){.value_assignment = node}, VALUE_ASSIGNMENT);

    return node;
}