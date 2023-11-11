/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_TOKEN_H
#define MPIR_COMPILER_MPIR_TOKEN_H

#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include "../mpir_misc/mpir_warnings.h"

#define TOKEN_NAME_MAP \
    "OP_MULTIPLY", "OP_DIVIDE", "OP_SUM", "OP_SUBTRACT", "OP_POWER", "OPEN_BRACKET", "CLOSED_BRACKET", "OPEN_BRACE", "CLOSE_BRACE", "QUANTIFIER_UNIVERSAL", "QUANTIFIER_EXISTENTIAL", \
    "OPERATOR_EQ", "OPERATOR_GT", "OPERATOR_LT", "OPERATOR_GTEQ", "OPERATOR_LTEQ", "COMMENT", "NUMERICAL_LITERAL", "STRING_LITERAL", "OPERATOR", "IDENTIFIER", "KEYWORD", "NEWLINE"

typedef enum
{
    /* Operators */
    operator_multiply,
    operator_divide,
    operator_sum,
    operator_subtract,
    operator_power,

    /* Brackets */
    open_bracket,
    close_bracket,
    open_brace,
    close_brace,

    /* Quantifiers */
    quantifier_universal,
    quantifier_existential,

    /* Boolean Comparator Operators */
    operator_eq,
    operator_gt,
    operator_lt,
    operator_gteq,
    operator_lteq,

    COMMENT,
    NUMERICAL_LITERAL,
    STRING_LITERAL,
    OPERATOR,
    IDENTIFIER,
    KEYWORD,
    NEWLINE
} mpir_token_type;

typedef struct
{
    /* Type of the token (e.g., number, operator, identifier, etc.) */
    mpir_token_type type;

    /* Lexeme of the token (actual value as a string) */
    wchar_t lexeme[128];

    /* Line number in the source code where the token appears */
    unsigned long int line_index;
    unsigned long int column_index;

} mpir_token;

#endif
