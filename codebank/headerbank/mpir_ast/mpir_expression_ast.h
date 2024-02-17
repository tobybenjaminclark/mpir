/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_EXPRESSION_AST_H
#define MPIR_COMPILER_MPIR_EXPRESSION_AST_H

#include "../../headerbank/mpir_token/mpir_token.h"
#include <stdbool.h>

/* Defining Macros for expression types */
#define AST_IDENTIFIER 1
#define AST_NUMERICAL_LITERAL 2
#define AST_STRING_LITERAL 3
#define AST_FUNCTION_CALL 4
#define AST_OPERATOR 5



/**
 * @struct mpir_ast_identifier
 * @brief Structure representing an identifier in the Abstract Syntax Tree (AST).
 */
struct mpir_ast_identifier
{
    wchar_t data[128]; /** ← Data associated with the identifier. */
};



/**
 * @struct mpir_ast_type
 * @brief Structure representing a type in the Abstract Syntax Tree (AST).
 */
struct mpir_ast_type
{
    wchar_t data[128];  /** ← Data associated with the type. */
};



/**
 * @struct mpir_ast_function_identifier
 * @brief Structure representing a expression identifier in the Abstract Syntax Tree (AST).
 */
struct mpir_ast_function_identifier
{
    wchar_t data[128];  /** ← Data associated with the expression identifier. */
};



/**
 * @struct mpir_ast_function_call
 * @brief Structure representing a expression call in the Abstract Syntax Tree (AST).
 */
struct mpir_ast_function_call
{
    struct mpir_ast_function_identifier* identifier;      /** ← Function identifier for the call.         */
    struct mpir_ast_expression** arguments;               /** ← Array of arguments for the expression call. */
};



/**
 * @struct mpir_ast_expression
 * @brief Node structure for the Abstract Syntax Tree (AST).
 */
struct mpir_ast_expression
{
    int type;                                             /** ← Type of expression.                       */
    union {
        struct mpir_ast_function_call* function_call;     /** ← Data for a expression call expression.      */
        long double numerical_literal;                    /** ← Data for a numerical literal expression.  */
        wchar_t identifier[128];                          /** ← Data for an identifier expression.        */
        wchar_t string_literal[128];                      /** ← Data for a string literal expression.     */
        wchar_t operator[128];                            /** ← Data for an operator expression.          */
    } data;                                               /** ← Union of possible expression data.        */
    struct mpir_ast_expression* left;                     /** ← Pointer to the left subexpression.        */
    struct mpir_ast_expression* right;                    /** ← Pointer to the right subexpression.       */
};



#endif
