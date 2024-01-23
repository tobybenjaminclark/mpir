/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../../headerbank/mpir_parser/mpir_parsers/mpir_parse_on.h"

struct mpir_on_statement* parse_on_statement(mpir_parser* psr)
{
    /* Parse Indentation then parse `on` keyword */
    while(psr->peek(psr)->type == indentation)(void)psr->get(psr);
    if(psr->peek(psr)->type == keyword_on) (void)psr->get(psr);
    else return NULL;

    /* Parse & discard `on` keyword */
    struct mpir_on_statement* node = calloc(1, sizeof(struct mpir_on_statement));

    printf("PARSED ON!\n102");

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
            /* check for inbuilt call */
            return NULL;
    }

    /* Parse & discard newline */
    if(psr->peek(psr)->type == NEWLINE)(void)psr->get(psr);
    else return NULL;

    node->commands = command;
    return node;
}