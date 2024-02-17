/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PARSE_DO_H
#define MPIR_COMPILER_MPIR_PARSE_DO_H

#include "../mpir_parser.h"
#include "../mpir_parse_multiple.h"
#include "mpir_parse_let_binding.h"
#include "mpir_parse_set_binding.h"
#include "mpir_parse_function_call.h"
#include "mpir_parse_on.h"

/**
 * @brief Parses a do statement within the MPIR parser.
 *
 * This expression parses a `do` statement from the provided MPIR parser, including the associated expression call
 * and the following list of `on` statements. It creates, allocates and returns a `mpir_ast_do_statement` structure,
 * which gets returned. The statement is parsed in accoradance with the MPIR grammar.
 *
 * @param psr Pointer to the parser structure.
 * @param nodes Pointer to the command list to which the parsed `do` statement will be appended.
 *
 * @return A pointer to a dynamically allocated `mpir_ast_do_statement` structure representing the parsed `do` statement.
 *         Returns NULL if the parsing fails or encounters an unexpected structure.
 */
struct mpir_ast_do_statement* parse_do(mpir_parser* psr, struct mpir_command_list* nodes);

#endif
