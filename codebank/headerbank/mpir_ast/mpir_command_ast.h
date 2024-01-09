/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_COMMAND_AST_H
#define MPIR_COMPILER_MPIR_COMMAND_AST_H

#include "../../headerbank/mpir_token/mpir_token.h"
#include "../../headerbank/mpir_ast/mpir_expression_ast.h"
#include "../mpir_misc/mpir_linked_list.h"

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

struct mpir_command_list;
struct mpir_on_statement
{
    union literal {
        float mpir_numerical_literal;
        wchar_t* mpir_string_literal;
    };
    enum stored_type{
        numerical_literal,
        string_literal,
    } type;
    struct mpir_command_list* commands;
};

struct mpir_trycast_statement
{
    struct mpir_identifier* dominant_variable;
    struct mpir_identifier* casted_variable;
    struct mpir_on_statement** actions;
};


#endif
