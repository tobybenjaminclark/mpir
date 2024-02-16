/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PARSE_FUNCTION_BODY_H
#define MPIR_COMPILER_MPIR_PARSE_FUNCTION_BODY_H

#include "../../mpir_ast/mpir_command_ast.h"
#include "../../mpir_ast/mpir_ast.h"
#include "../../mpir_misc/mpir_linked_list.h"
#include "../mpir_parser.h"
#include "../mpir_parser_utilities.h"
#include "mpir_parse_expression.h"
#include "mpir_parse_set_binding.h"
#include "mpir_parse_let_binding.h"
#include "mpir_parse_do.h"
#include "mpir_parse_trycast.h"
#include "../mpir_parse_multiple.h"
#include "mpir_parse_on.h"

struct mpir_command_list* parse_function_body(mpir_parser* psr, struct mpir_command_list* nodes);

#endif
