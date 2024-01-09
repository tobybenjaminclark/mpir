/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PARSER_UTILITIES_H
#define MPIR_COMPILER_MPIR_PARSER_UTILITIES_H

#include "../../headerbank/mpir_parser/mpir_parser.h"
#include "stdbool.h"

struct mpir_identifier* parse_identifier(mpir_parser* psr);
struct mpir_type* parse_returntype(mpir_parser* psr);
struct mpir_type* parse_type(mpir_parser* psr);
struct mpir_function_identifier* parse_function_identifier(mpir_parser* psr);

#endif
