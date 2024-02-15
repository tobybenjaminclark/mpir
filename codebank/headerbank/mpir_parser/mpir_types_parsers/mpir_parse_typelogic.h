/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PARSE_TYPELOGIC_H
#define MPIR_COMPILER_MPIR_PARSE_TYPELOGIC_H

#include "../mpir_parser.h"
#include "../../../headerbank/mpir_ast/mpir_ast.h"
#include "../mpir_parser_utilities.h"
#include "../mpir_parse_multiple.h"
#include "../mpir_doc_parsers/mpir_parse_docsection.h"

struct boolean_logic_token{
    mpir_token** tokens;
    int token_count;
    struct boolean_logic_token* left;
    struct boolean_logic_token* right;
};

void print_type_logic(struct type_logic* node);
struct mpir_type_logic* parse_type_logic(mpir_parser* psr);

#endif
