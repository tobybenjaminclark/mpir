/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PARSE_SET_BINDING_H
#define MPIR_COMPILER_MPIR_PARSE_SET_BINDING_H

#include "../mpir_parser.h"
#include "mpir_parse_expression.h"

/**
 * @brief Function to parse a 'set' binding (value assignment) within the MPIR parser.
 *
 * This function parses a 'set' binding within the context of the MPIR. A 'set' binding involves assigning a value to a
 * variable with a specified type. The function sequentially parses the 'set' keyword, the variable identifier, the 'as'
 * keyword, and the associated expression (value). It then creates and returns a dynamically allocated
 * `struct mpir_value_assignment` representing the parsed 'set' binding.
 *
 * @param psr A pointer to the MPIR parser structure.
 * @param nodes A pointer to a mpir_command_list structure containing the list of current commands.
 * @return A pointer to a dynamically allocated `struct mpir_value_assignment` on successful parsing.
 */
struct mpir_value_assignment* parse_set_binding(mpir_parser* psr, struct mpir_command_list* nodes);

#endif
