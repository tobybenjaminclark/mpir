/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../../headerbank/mpir_parser/mpir_func_parsers/mpir_parse_on.h"

/**
 * @brief Parses an 'on' statement within the MPiR parser.
 *
 * This function parses an 'on' statement, which is used in the context of MPiR to specify actions to be taken
 * based on certain conditions. The 'on' statement starts with the 'on' keyword followed by a literal value,
 * an arrow '->', and a command. The function creates and returns a dynamically allocated `struct mpir_ast_on_statement`
 * representing the parsed 'on' statement as part of the AST.
 *
 * @param psr A pointer to the MPiR parser structure.
 * @return Pointer to a dynamically allocated `struct mpir_ast_on_statement` or NULL on failure.
 */
struct mpir_ast_on_statement* parse_on_statement(mpir_parser* psr)
{
    /* Parse Indentation then parse `on` keyword */
    while(psr->peek(psr)->type == indentation)(void)psr->get(psr);

    if(psr->peek(psr)->type == keyword_on) (void)psr->get(psr);
    else return NULL;

    /* Parse & discard `on` keyword */
    struct mpir_ast_on_statement* node = calloc(1, sizeof(struct mpir_ast_on_statement));

    /* Parse literals */
    switch(psr->peek(psr)->type)
    {
        case NUMERICAL_LITERAL:
            node->stored_type = numerical_literal;
            node->literal.mpir_numerical_literal = wcstod(psr->get(psr)->lexeme, NULL);
            break;
        case STRING_LITERAL:
            node->stored_type = string_literal;
            wcscpy(node->literal.mpir_string_literal, psr->get(psr)->lexeme);
            break;
        default:
            return NULL;
    }

    /* Parse & discard arrow */
    if(psr->peek(psr)->type = operator_arrow) (void)psr->get(psr);
    else return NULL;
    printf("PARSED ARROW!\n");
    /* Setup Command List Structure */
    struct mpir_command_list* command;
    command = initialize_command_list();

    /* Parse Command */
    switch(psr->peek(psr)->type)
    {
        case keyword_let:
            parse_let_binding(psr, command);
            break;
        case keyword_set:
            parse_set_binding(psr, command);
            printf("Parsed set binding!");
            break;
        case IDENTIFIER:
            break;
        default:
            return NULL;
    }

    /* Parse & discard newline */
    if(psr->peek(psr)->type == NEWLINE)(void)psr->get(psr);
    else return NULL;

    node->commands = command;
    return node;
}