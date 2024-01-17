/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_EXPRESSION_AST_H
#define MPIR_COMPILER_MPIR_EXPRESSION_AST_H

#include "../../headerbank/mpir_token/mpir_token.h"
#include <stdbool.h>

#define AST_IDENTIFIER 1
#define AST_NUMERICAL_LITERAL 2
#define AST_STRING_LITERAL 3
#define AST_FUNCTION_CALL 4
#define AST_OPERATOR 5



struct mpir_identifier
{
    wchar_t data[128];
};



struct mpir_type
{
    wchar_t data[128];
};



struct mpir_function_identifier
{
    wchar_t data[128];
};



struct mpir_function_call{
    struct mpir_function_identifier* identifier;
    struct mpir_identifier** arguments;
};



// Node structure for the Abstract Syntax Tree (AST)
struct mpir_expression
{
    int type;                  // 'n' for number, 'o' for operator
    union {
        struct mpir_function_call* function_call;
        long double numerical_literal;
        wchar_t identifier[128];
        wchar_t string_literal[128];
        wchar_t operator[128];
    } data;
    struct Node* left;          // left child
    struct Node* right;         // right child
};

#endif
