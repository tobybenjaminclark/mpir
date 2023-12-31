/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_TOKENISER_APPEND_H
#define MPIR_COMPILER_MPIR_TOKENISER_APPEND_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../../headerbank/mpir_tokeniser/mpir_lexer.h"
#include "../../headerbank/mpir_token/mpir_token.h"

void mpir_lexer_append_token(mpir_lexer *lexer, mpir_token *token);

#endif
