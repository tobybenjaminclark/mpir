/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PARSER_H
#define MPIR_COMPILER_MPIR_PARSER_H

#include "../../headerbank/mpir_token/mpir_token.h"

typedef struct {
    unsigned long int current_index;
} mpir_parser;

void mpir_parse(mpir_token** list_of_tokens);

#endif
