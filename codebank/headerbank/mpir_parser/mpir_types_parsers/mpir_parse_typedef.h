/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PARSE_TYPEDEF_H
#define MPIR_COMPILER_MPIR_PARSE_TYPEDEF_H

#include "../mpir_parser.h"
#include "../mpir_parser_utilities.h"
#include "../mpir_parse_multiple.h"
#include "../mpir_doc_parsers/mpir_parse_docsection.h"
#include "mpir_parse_typelogic.h"

bool parse_type_declaration(mpir_parser* psr);

#endif
