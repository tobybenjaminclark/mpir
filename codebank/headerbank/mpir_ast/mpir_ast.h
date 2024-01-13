/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_AST_H
#define MPIR_COMPILER_MPIR_AST_H

#include "../../headerbank/mpir_token/mpir_token.h"
#include "../../headerbank/mpir_ast/mpir_command_ast.h"
#include "../../headerbank/mpir_misc/mpir_linked_list.h"

struct mpir_function_declaration
{
    struct mpir_identifier* identifier;
    struct mpir_type** inputs;
    struct mpir_type* return_type;
    struct mpir_command_list* body;
};

struct mpir_type_declaration
{
    struct mpir_identifier* identifier;
    struct mpir_type** inputs;
    struct mpir_type* base_type;
};

#endif
