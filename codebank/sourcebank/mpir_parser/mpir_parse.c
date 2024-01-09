/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_parser/mpir_parse.h"

void mpir_parse(mpir_parser* parser)
{
    mpir_token_type next_type;
    mpir_token* current_token = parser->get(parser);
    while(current_token != NULL)
    {
        if(parser->peek(parser) != NULL)
        {
            next_type = (parser->peek(parser))->type;
            if(next_type == keyword_funcdef)
            {
                printf("branching to parse_function_declaration!\n");
                parse_function_declaration(parser);
            }
        }
        else next_type = (mpir_token_type) NULL;

        current_token = parser->get(parser);
    }
    return;
}