/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_parser/mpir_parser_utilities.h"

struct mpir_identifier* parse_identifier(mpir_parser* psr)
{
    struct mpir_identifier node;
    if((psr->peek(psr))->type != IDENTIFIER)
    {
        mpir_error("parse_function_declaration: expected function identifier got other.");
        return NULL;
    }
    else wcscpy(node.data, (psr->get(psr))->lexeme);
    return &node;
}

struct mpir_function_identifier* parse_function_identifier(mpir_parser* psr)
{
    struct mpir_function_identifier node;
    if(psr->peek(psr)->type == IDENTIFIER) wcscpy(node.data, (psr->get(psr))->lexeme);
    else return NULL;
    return &node;
}


struct mpir_type* parse_returntype(mpir_parser* psr)
{
    struct mpir_type node;
    if((psr->peek(psr))->type != IDENTIFIER)
    {
        mpir_error("parse_function_declaration: expected function returntype got other.");
        return NULL;
    }
    else wcscpy(node.data, (psr->get(psr))->lexeme);
    wprintf(L"Parsed Return Type of '%ls' \n", node.data);
    return &node;
}

struct mpir_type* parse_type(mpir_parser* psr)
{
    struct mpir_type node;
    if((psr->peek(psr))->type != IDENTIFIER)
    {
        mpir_error("parse_function_declaration: expected function type got other.");
        return NULL;
    }

    else if((psr->peek(psr))->type == IDENTIFIER)
    {
        wcscpy(node.data, (psr->get(psr))->lexeme);
        wprintf(L"Type Identifier '%ls' \n", node.data);
        return &node;
    }
    else return NULL;
}