/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PARSE_FUNCTION_HEADER_H
#define MPIR_COMPILER_MPIR_PARSE_FUNCTION_HEADER_H

#include "../../headerbank/mpir_parser/mpir_parser.h"
#include "../../headerbank/mpir_parser/mpir_parser_utilities.h"
#include "../../headerbank/mpir_parser/mpir_parse_function_body.h"


/**
 * @brief Internal Function to parse a list of input types within a function declaration recursively.
 *
 * This recursive function parses a series of input types in the context of a function declaration. It expects
 * identifiers representing input types separated by commas. The parsing process involves allocating memory for a
 * dynamic array of `mpir_type` struct pointers. The function recursively calls itself when encountering multiple input
 * types, and it terminates when it encounters the '->' operator, indicating the end of the input types section.
 *
 * @param psr A pointer to the MPIR parser structure.
 * @param nodes  A pointer to an array of `mpir_type` structures, may be reallocated.
 * @param node_index The index indicating the current position in the 'nodes' array.
 *
 * @return A pointer to the array of parsed input types on success or NULL on parsing failure.
 */
struct mpir_type** parse_inputs_internal(mpir_parser* psr, struct mpir_type** nodes, int node_index);


/**
 * @brief Function to parse Function IO Input Types, returns a list of mpir_type structures
 *
 * This function is responsible for parsing the declaration of function input types. It does this using the `parse_
 * inputs_internal()` function, which uses a recursive approach. Memory is allocated for this list dynamically,
 * meaning a function can take any (*reasonable) number of arguments.
 *
 * @param psr A pointer to the MPIR parser structure.
 * @return List of Inputs on success, NULL on parsing failure.
 */
struct mpir_type** parse_inputs(mpir_parser* psr);


/**
 * @brief Function to parse a Function Header, returns a mpir_function_declaration structure.
 *
 * This function is responsible for parsing the declaration of a function according to the MPIR Grammar. It gathers
 * the identifier, input types, and output types. Performs memory allocation for the list of input types. The decl.
 * is added to the declaration list in the parser. The grammar can be seen below, and also in the CFG documentation.
 * `funcdef' identifier '::' function_io '\n'`
 *
 * @param psr A pointer to the MPIR parser structure.
 * @return True on parsing success, False on parsing failure.
 *
 * @brief Function to parse Function IO Input Types, returns a list of mpir_type structures
 *
 * This function is responsible for parsing the declaration of function input types. It does this using the `parse_
 * inputs_internal()` function, which uses a recursive approach. Memory is allocated for this list dynamically,
 * meaning a function can take any (*reasonable) number of arguments.
 *
 * @param psr A pointer to the MPIR parser structure.
 * @return List of Inputs on success, NULL on parsing failure.
 */
bool parse_function_declaration(mpir_parser* psr);


#endif
