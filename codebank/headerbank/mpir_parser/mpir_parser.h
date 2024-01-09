/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PARSER_H
#define MPIR_COMPILER_MPIR_PARSER_H

#include "../../headerbank/mpir_token/mpir_token.h"
#include "../../headerbank/mpir_token/mpir_token_write.h"
#include "../../headerbank/mpir_tokeniser/mpir_lexer.h"
#include "../../headerbank/mpir_ast/mpir_ast.h"
#include "../../headerbank/mpir_misc/mpir_linked_list.h"
#include "../../headerbank/mpir_misc/mpir_definition_list.h"

struct mpir_parser{
    unsigned long int token_count;
    unsigned long int token_index;
    mpir_token** tokens;

    /* Program */
    struct mpir_declaration_list* program;

    /* Function Pointers */
    mpir_token* (*get)(struct mpir_parser *parser);
    mpir_token* (*peek)(struct mpir_parser *parser);
    mpir_token* (*tryget)(struct mpir_parser *parser, mpir_token_type type);
};

typedef struct mpir_parser mpir_parser;

mpir_token* mpir_parser_peek(mpir_parser* parser);
mpir_token* mpir_parser_get(mpir_parser* parser);
mpir_token* mpir_parser_tryget(mpir_parser* parser, mpir_token_type type);

mpir_parser* upgrade_to_parser(mpir_lexer* lexer);
void mpir_parser_free(mpir_parser* parser);
void mpir_parse(mpir_parser* parser);

#endif
