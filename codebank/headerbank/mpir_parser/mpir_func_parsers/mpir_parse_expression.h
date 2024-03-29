/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PARSE_EXPRESSION_H
#define MPIR_COMPILER_MPIR_PARSE_EXPRESSION_H

#include "../../mpir_ast/mpir_ast.h"
#include "../../mpir_token/mpir_token.h"
#include "../mpir_parser.h"
#include "../mpir_parser_utilities.h"
#include "../mpir_parse_multiple.h"

#include <wchar.h>
#include <stdio.h>

struct mpir_ast_expression* get_arg(mpir_parser* psr);

struct mpir_ast_identifier** parse_arguments(mpir_parser* psr);
struct mpir_ast_function_call* mpir_parse_function_call(mpir_parser* psr);

// Function to build the AST from the expression
struct mpir_ast_expression* mpir_parse_expression(mpir_parser* psr, mpir_token_type delimiter_type, int minimum_precedence);

// Helper expression to perform arithmetic operations
double performOperation(double operand1, char operator, double operand2);

// Helper expression to check if a character is an operator
int isOperator(char ch);

// Helper expression to get the precedence of an operator
int mpir_get_op_presedence(mpir_token_type operator);

void mpir_display_ast(struct mpir_ast_expression* root, int indentation_level);

#endif
