/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PARSE_FUNCTION_CALL_H
#define MPIR_COMPILER_MPIR_PARSE_FUNCTION_CALL_H

#include "../mpir_parser.h"
#include "../mpir_parse_multiple.h"
#include "mpir_parse_expression.h"

/**
 * @brief Parses a Function Call, returns a pointer to a mpir_function_call structure.
 *
 * This function attempts to parse a function call from the provided parser, verifying its structure according to the
 * MPIR grammar. It allocates memory for both the parser, and the input expressions (using the expression parser), the
 * grammar can be seen in the CFG Documentation or as follows: identifier `(` expr0 `,` expr1 `,` ... exprN )
 *
 * @param psr Pointer to the MPIR parser structure.
 * @return A pointer to a dynamically allocated `mpir_function_call` structure representing the parsed function call.
 *         Returns NULL if the parsing fails or encounters an unexpected structure.
 */
struct mpir_function_call* mpir_parse_function_call(mpir_parser* psr);

#endif
