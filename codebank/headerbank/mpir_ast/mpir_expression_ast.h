/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_EXPRESSION_AST_H
#define MPIR_COMPILER_MPIR_EXPRESSION_AST_H

#include "../../headerbank/mpir_token/mpir_token.h"
#include <stdbool.h>

struct mpir_identifier
{
    wchar_t* data[128];
};

struct mpir_type
{
    wchar_t* data[128];
};

struct mpir_function_identifier
{
    wchar_t* data[128];
};

struct mpir_function_call{
    struct mpir_function_identifier* identifier;
    struct mpir_identifier** arguments;
};

struct mpir_expression{
    union {
        struct mpir_function_call* function_call;
        long double numerical_literal;
        wchar_t* identifier;
        wchar_t* string_literal;
    } data;
    struct mpir_ast* left;
    struct mpir_ast* right;
};

#endif
