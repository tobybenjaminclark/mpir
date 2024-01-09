/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PARSE_EXPRESSION_H
#define MPIR_COMPILER_MPIR_PARSE_EXPRESSION_H

#include "../../headerbank/mpir_ast/mpir_ast.h"
#include "../../headerbank/mpir_token/mpir_token.h"
#include "../../headerbank/mpir_parser/mpir_parser.h"
#include "../../headerbank/mpir_parser/mpir_parser_utilities.h"

struct mpir_expression* mpir_parse_expression(mpir_parser* psr);

struct mpir_identifier** parse_arguments_internal(mpir_parser* psr, struct mpir_identifier** nodes, int node_index);
struct mpir_identifier** parse_arguments(mpir_parser* psr);
struct mpir_function_call* mpir_parse_function_call(mpir_parser* psr);

#endif //MPIR_COMPILER_MPIR_PARSE_EXPRESSION_H
