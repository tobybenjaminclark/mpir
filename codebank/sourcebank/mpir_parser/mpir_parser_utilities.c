/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_parser/mpir_parser_utilities.h"

struct mpir_identifier* parse_identifier(mpir_parser* psr)
{
    struct mpir_identifier* node = malloc(sizeof(struct mpir_identifier));
    if((psr->peek(psr))->type != IDENTIFIER)
    {
        mpir_error("parse_function_declaration: expected function identifier got other.");
        return NULL;
    }
    else
    {
        node->data[0] = L'\0';
        wcscpy((wchar_t *) node->data, (psr->get(psr))->lexeme);
    }
    return node;
}


struct mpir_function_identifier* parse_function_identifier(mpir_parser* psr)
{
    struct mpir_function_identifier* node = malloc(sizeof(struct mpir_function_identifier));
    if(psr->peek(psr)->type == IDENTIFIER)
    {
        node->data[0] = L'\0';
        wcscpy(node->data, (psr->get(psr))->lexeme);
    }
    else return NULL;
    return node;
}


struct mpir_type* parse_returntype(mpir_parser* psr)
{
    struct mpir_type* node = malloc(sizeof(struct mpir_type));
    if((psr->peek(psr))->type != IDENTIFIER)
    {
        mpir_error("parse_function_declaration: expected function identifier got other.");
        return NULL;
    }
    else
    {
        node->data[0] = L'\0';
        wcscpy((wchar_t *) node->data, (psr->get(psr))->lexeme);
    }
    return node;
}


struct mpir_type* parse_type(mpir_parser* psr)
{
    struct mpir_type* node = malloc(sizeof(struct mpir_type));
    if((psr->peek(psr))->type != IDENTIFIER)
    {
        mpir_error("parse_function_declaration: expected function type got other.");
        return NULL;
    }

    else if((psr->peek(psr))->type == IDENTIFIER)
    {
        node->data[0] = L'\0';
        wcscpy(node->data, (psr->get(psr))->lexeme);
        return node;
    }
    else return NULL;
}



struct mpir_type* get_type(mpir_parser* psr)
{
    if(psr->peek(psr)->type != IDENTIFIER) return NULL;

    struct mpir_type* arg = calloc(1, sizeof (struct mpir_identifier));
    wcscpy(arg->data, psr->get(psr)->lexeme);
    if(psr->peek(psr)->type == keyword_comma) (void)psr->get(psr);
    return arg;
}