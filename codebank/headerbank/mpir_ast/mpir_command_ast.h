/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_COMMAND_AST_H
#define MPIR_COMPILER_MPIR_COMMAND_AST_H

#include "../../headerbank/mpir_token/mpir_token.h"
#include "../../headerbank/mpir_ast/mpir_expression_ast.h"

struct mpir_type_assignment
{
    struct mpir_identifier* identifier;
    struct mpir_type* type;
};

struct mpir_value_assignment
{
    struct mpir_identifier* identifier;
    struct mpir_expression* expression;
};

#endif //MPIR_COMPILER_MPIR_COMMAND_AST_H
