/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../../headerbank/mpir_parser/mpir_parsers/mpir_parse_function_body.h"


struct mpir_do_statement* parse_do(mpir_parser* psr, struct mpir_command_list* nodes)
{
    struct mpir_do_statement* node = malloc(sizeof (struct mpir_do_statement));

    /* Parse & discard `do` keyword. */
    if(psr->peek(psr)->type == keyword_do) (void)psr->get(psr);
    else return NULL;

    /* Try to parse function call */
    if((node->function = mpir_parse_function_call(psr)) == NULL) return NULL;

    /* Parse & discard newline. */
    if(psr->peek(psr)->type == NEWLINE) (void)psr->get(psr);
    else return NULL;

    /* Parse on statements */
    node->actions = PARSE_MULTIPLE_STATEMENTS(struct mpir_on_statement, parse_on_statement, psr);
    if(node->actions == NULL) return NULL;

    append_command(nodes, (union mpir_command_data){.do_statement = node}, DO_STATEMENT);
    return node;
}


struct mpir_command_list* parse_function_body(mpir_parser* psr)
{
    /* Setup & Allocate Memory for Command List */
    char* token_names[] = {TOKEN_NAME_MAP};
    struct mpir_command_list* nodes = initialize_command_list();
    mpir_token_type ntt;

    while ((ntt = psr->peek(psr)->type) != keyword_suchthat)
    {
        wprintf(L"Next Token Type is %s \n", token_names[ntt]);
        switch (ntt)
        {
        case keyword_let:
            parse_let_binding(psr, nodes);
            break;
        case keyword_set:
            parse_set_binding(psr, nodes);
            break;
        case keyword_trycast:
            parse_trycast(psr, nodes);
            break;
        case IDENTIFIER:
            {};
            struct mpir_function_call* a = mpir_parse_function_call(psr);
            if(a != NULL)
            {
                append_command(nodes, (union mpir_command_data){.function_call = a}, FUNCTION_CALL);
            }
            break;
        default:
            (void)psr->get(psr);
        }
    }

    return nodes;
}