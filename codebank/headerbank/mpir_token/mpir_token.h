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
    "*", "/", "+", "-", "^", "=", "(", ")", \
    "{", "}", "QUANTIFIER_UNIVERSAL", "QUANTIFIER_EXISTENTIAL", "=", ">",    \
    "<", ">=", "<=", "→", "↔", "^", "¬",        \
    "∨", "using", "suchthat", "funcdef", "typedef", "trycast", "into", "do", "on", "let", "set", "in", "as", "end", ",",   \
    "____", "|", ":", "::", "COMMENT", "NUMERICAL_LITERAL", "STRING_LITERAL", "IDENTIFIER", "KEYWORD", "NEWLINE"


typedef enum
{
    /* Operators */
    operator_multiply,
    operator_divide,
    operator_sum,
    operator_subtract,
    operator_power,
    operator_equals,

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

    /* Connective Operators */
    operator_arrow,
    operator_bi_arrow,
    operator_not,
    operator_and,
    operator_or,

    /* Keywords */
    keyword_using,
    keyword_suchthat,
    keyword_funcdef,
    keyword_typedef,
    keyword_trycast,
    keyword_into,
    keyword_do,
    keyword_on,
    keyword_let,
    keyword_set,
    keyword_in,
    keyword_as,
    keyword_end,
    keyword_comma,

    /* Indentation */
    indentation,
    pipesymb,
    colon,
    double_colon,

    COMMENT,
    NUMERICAL_LITERAL,
    STRING_LITERAL,
    IDENTIFIER,
    KEYWORD,
    NEWLINE
} mpir_token_type;

typedef struct
{
    mpir_token_type type;                   /* Enumeration type of the token instance.      */
    wchar_t lexeme[128];                    /* String of the token instance.                */
    unsigned long int line_index;           /* Line index of the token instance.            */
    unsigned long int column_index;         /* Column index of the token instance.          */
} mpir_token;

#endif
