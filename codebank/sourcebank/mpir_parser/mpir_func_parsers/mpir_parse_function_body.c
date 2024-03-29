/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../../headerbank/mpir_parser/mpir_func_parsers/mpir_parse_function_header.h"




struct mpir_command_list* parse_function_body(mpir_parser* psr, struct mpir_command_list* nodes)
{
    /* Setup & Allocate Memory for Command List */
    char* token_names[] = {TOKEN_NAME_MAP};
    mpir_token_type ntt;

    /* Parse Statements */
    while ((ntt = psr->peek(psr)->type) != keyword_suchthat && psr->peek(psr)->type != keyword_end)
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
        case keyword_do:
            parse_do(psr, nodes);
            break;
        case IDENTIFIER:
            {};
            struct mpir_ast_function_call* a = mpir_parse_function_call(psr);
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