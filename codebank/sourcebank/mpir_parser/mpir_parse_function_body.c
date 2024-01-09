/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_parser/mpir_parse_function_body.h"

struct mpir_type_assignment* parse_let_binding(mpir_parser* psr)
{
    struct mpir_type_assignment node;

    /* Parse `let` */
    if(psr->peek(psr)->type == keyword_let) (void)psr->get(psr);
    else return NULL;

    /* Parse variable identifier */
    if(psr->peek(psr)->type == IDENTIFIER) node.identifier = parse_type(psr);
    else return NULL;
    if(node.identifier == NULL) return NULL;

    /* Parse `as` */
    if(psr->peek(psr)->type == keyword_as) (void)psr->get(psr);
    else return NULL;

    /* Parse type identifier */
    if(psr->peek(psr)->type == IDENTIFIER) node.type = parse_type(psr);
    else return NULL;
    if(node.type == NULL) return NULL;

    return &node;
}

struct mpir_value_assignment* parse_set_binding(mpir_parser* psr)
{
    struct mpir_value_assignment node;

    /* Parse `set` */
    if(psr->peek(psr)->type == keyword_set) (void)psr->get(psr);
    else return NULL;

    /* Parse variable identifier */
    if(psr->peek(psr)->type == IDENTIFIER) node.identifier = parse_type(psr);
    else return NULL;
    if(node.identifier == NULL) return NULL;

    /* Parse `as` */
    if(psr->peek(psr)->type == keyword_as) (void)psr->get(psr);
    else return NULL;

    /* Parse type identifier */
    node.expression = mpir_parse_expression(psr);
    if(node.expression == NULL) return NULL;

    return &node;
}

struct mpir_trycast_statement* parse_trycast(mpir_parser* psr)
{
    struct mpir_trycast_statement node;

    /* Parse & Discard `Keyword` Variable */
    if(psr->peek(psr)->type == keyword_trycast) (void)psr->get(psr);
    else return NULL;

    /* Parse Dominant Variable */
    node.dominant_variable = parse_identifier(psr);
    if(node.dominant_variable == NULL) return NULL;

    /* Parse & Discard `into` keyword */
    if(psr->peek(psr)->type == keyword_into) (void)psr->get(psr);
    else return NULL;

    /* Parse 2nd Identifier (casted variable) */
    node.casted_variable = parse_identifier(psr);
    if(node.casted_variable == NULL) return NULL;

    /* Parse `\n` */
    if(psr->peek(psr)->type == NEWLINE) (void)psr->get(psr);
    else return NULL;

    /* Parse `on` statements */
    while(psr->peek(psr)->type == keyword_on)
    {
        /* parse_on_statement; */
        /* `on` literal/variable `->` function_call | assignment */
        NULL;
    }

    return &node;
}

struct mpir_command_list* parse_function_body(mpir_parser* psr)
{
    /*
     * (let <|> set <|> parse_function_body) '\n'
     */
    return NULL;
}