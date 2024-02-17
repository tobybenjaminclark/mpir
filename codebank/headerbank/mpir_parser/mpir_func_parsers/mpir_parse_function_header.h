/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PARSE_FUNCTION_HEADER_H
#define MPIR_COMPILER_MPIR_PARSE_FUNCTION_HEADER_H

#include "../mpir_parser.h"
#include "../mpir_parser_utilities.h"
#include "mpir_parse_function_body.h"
#include "../mpir_parse_multiple.h"
#include "../mpir_doc_parsers/mpir_parse_docsection.h"

struct mpir_ast_type* get_input(mpir_parser* psr);
struct mpir_ast_type** parse_inputs(mpir_parser* psr);

/**
 * @brief Function to parse a Function Header, returns a mpir_ast_function_declaration structure.
 *
 * This expression is responsible for parsing the declaration of a expression according to the MPIR Grammar. It gathers
 * the identifier, input types, and output types. Performs memory allocation for the list of input types. The decl.
 * is added to the declaration list in the parser. The grammar can be seen below, and also in the CFG documentation.
 * `funcdef' identifier '::' function_io '\n'`
 *
 * @param psr A pointer to the MPIR parser structure.
 * @return True on parsing success, False on parsing failure.
 *
 * @brief Function to parse Function IO Input Types, returns a list of mpir_ast_type structures
 *
 * This expression is responsible for parsing the declaration of expression input types. It does this using the `parse_
 * inputs_internal()` expression, which uses a recursive approach. Memory is allocated for this list dynamically,
 * meaning a expression can take any (*reasonable) number of arguments.
 *
 * @param psr A pointer to the MPIR parser structure.
 * @return List of Inputs on success, NULL on parsing failure.
 */
bool parse_function_declaration(mpir_parser* psr);


#endif
