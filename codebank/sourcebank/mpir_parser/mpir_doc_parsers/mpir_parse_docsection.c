/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../../headerbank/mpir_parser/mpir_doc_parsers/mpir_parse_docsection.h"

struct mpir_doc* mpir_parse_doc(mpir_parser* psr)
{
    struct mpir_doc* node = calloc(1, sizeof(struct mpir_doc));

    /* identifier maybe(identifier) 'as' string_literal */
    if(psr->peek(psr) == IDENTIFIER) node->flag_type = parse_identifier(psr);
    if(node->flag_type == NULL) return NULL;

    /* parse identifier (if exists) */
    if(psr->peek(psr)->type == IDENTIFIER) wcscpy(node->variable, psr->get(psr)->lexeme);

    /* parse as */
    if(psr->peek(psr)->type == keyword_as) (void)psr->get(psr);
    else return NULL;

    /* parse documentation */
    node->documentation = malloc(sizeof(psr->peek(psr)->lexeme));
    if(psr->peek(psr)->type == STRING_LITERAL) wcscpy(node->documentation, psr->get(psr)->lexeme);

    return NULL;
}

struct mpir_docsection* mpir_parse_docsection(mpir_parser* psr)
{
    /* suchthat: `\n` ( ____ `|` ____ doc `\n`)* end */
    return NULL;
}