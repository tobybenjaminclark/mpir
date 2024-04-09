/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../../headerbank/mpir_parser/mpir_types_parsers/mpir_parse_typelogic.h"

struct mpir_ast_expression* parse_type_logic(mpir_parser* psr)
{
    return mpir_parse_expression(psr, close_brace, 0);
}