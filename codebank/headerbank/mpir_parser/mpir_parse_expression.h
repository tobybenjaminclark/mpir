/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PARSE_EXPRESSION_H
#define MPIR_COMPILER_MPIR_PARSE_EXPRESSION_H

#include "../../headerbank/mpir_ast/mpir_ast.h"
#include "../../headerbank/mpir_token/mpir_token.h"
#include "../../headerbank/mpir_parser/mpir_parser.h"
#include "../../headerbank/mpir_parser/mpir_parser_utilities.h"
#include <wchar.h>
#include <stdio.h>

struct mpir_expression* mpir_parse_expression(mpir_parser* psr);
struct mpir_expression* parse_arithmetic_expression(mpir_parser* psr);
struct mpir_expression* parse_term(mpir_parser* psr);
struct mpir_expression* parse_factor(mpir_parser* psr);
struct mpir_identifier* get_arg(mpir_parser* psr);

struct mpir_identifier** parse_arguments(mpir_parser* psr);
struct mpir_function_call* mpir_parse_function_call(mpir_parser* psr);

// Function to build the AST from the expression
Node* buildAST(mpir_parser* psr, mpir_token_type delimiter_type);

// Helper function to perform arithmetic operations
double performOperation(double operand1, char operator, double operand2);

// Helper function to check if a character is an operator
int isOperator(char ch);

// Helper function to get the precedence of an operator
int getPrecedence(char operator);

void displayASTIndented(Node* root, int indentLevel);

#endif
