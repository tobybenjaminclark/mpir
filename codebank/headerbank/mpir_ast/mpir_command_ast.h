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

/**
 * @brief Structure representing a value assignment in the AST.
 *
 * Represents a `set` binding in the language, between a variable identifier and an expression. Please note that
 * the core calculus specifies that the type of the expression must reduce and be equal to the type of the bound
 * variable - otherwise a compile time type error will be thrown.
 *
 * @var mpir_value_assignment::identifier   Variable identifier that is being assigned a value.
 * @var mpir_value_assignment::expression   Expression to assign to the variable.
 */
struct mpir_value_assignment
{
    struct mpir_identifier* identifier;
    struct mpir_expression* expression;
};

struct mpir_command_list;
struct mpir_on_statement
{
    union {
        double mpir_numerical_literal;
        wchar_t* mpir_string_literal;
    } literal;
    enum stored_type{
        numerical_literal,
        string_literal,
    } stored_type;
    struct mpir_command_list* commands;
};

struct mpir_trycast_statement
{
    struct mpir_identifier* dominant_variable;
    struct mpir_identifier* casted_variable;
    struct mpir_on_statement** actions;
};

struct mpir_do_statement
{
    struct mpir_function_call* function;
    struct mpir_on_statement** actions;
};


#endif
