/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PARSE_DOCSECTION_H
#define MPIR_COMPILER_MPIR_PARSE_DOCSECTION_H

#include "../../mpir_ast/mpir_ast.h"
#include "../../mpir_parser/mpir_parser.h"
#include "../../mpir_parser/mpir_parser_utilities.h"

struct mpir_doc* mpir_parse_doc(mpir_parser* psr);
struct mpir_docsection* mpir_parse_docsection(mpir_parser* psr);

#endif
