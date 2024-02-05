/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PARSE_LET_BINDING_H
#define MPIR_COMPILER_MPIR_PARSE_LET_BINDING_H

#include "../mpir_parser.h"

/**
 * @brief Function to parse a 'let' binding (type assignment) within the MPIR parser.
 *
 * This function parses a 'let' binding within the context of MPIR. A 'let' binding involves declaring a variable
 * with a specified type. The function sequentially parses the 'let' keyword, the variable identifier, the 'as' keyword,
 * and the associated type identifier. It then creates and returns a dynamically allocated `struct mpir_ast_type_assignment`
 * representing the parsed 'let' binding as part of the AST.
 *
 * @param psr A pointer to the MPIR parser structure.
 * @nodes A pointer to a mpir_command_list structure containing the list of current commands.
 * @return A pointer to a dynamically allocated `struct mpir_ast_type_assignment` on successful parsing.
 */
struct mpir_ast_type_assignment* parse_let_binding(mpir_parser* psr, struct mpir_command_list* nodes);

#endif //MPIR_COMPILER_MPIR_PARSE_LET_BINDING_H
