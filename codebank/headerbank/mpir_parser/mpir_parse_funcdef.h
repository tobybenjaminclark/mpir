/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PARSE_FUNCDEF_H
#define MPIR_COMPILER_MPIR_PARSE_FUNCDEF_H

#include "../../headerbank/mpir_parser/mpir_parser.h"
#include "../../headerbank/mpir_parser/mpir_parser_utilities.h"

struct mpir_type** parse_inputs_internal(mpir_parser* psr, struct mpir_type** nodes, int node_index);
struct mpir_type** parse_inputs(mpir_parser* psr);
struct mpir_function_declaration* parse_function_declaration(mpir_parser* psr);

#endif //MPIR_COMPILER_MPIR_PARSE_FUNCDEF_H
