/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_LEXER_TOKEN_HANDLER_H
#define MPIR_COMPILER_MPIR_LEXER_TOKEN_HANDLER_H

#include <stdio.h>
#include <string.h>
#include <wchar.h>

#include "../../headerbank/mpir_token/mpir_token.h"
#include "../../headerbank/mpir_token/mpir_token_create.h"
#include "../../headerbank/mpir_lexicalization/mpir_tokeniser_append.h"

#define MPIR_KEYWORDS {"->", "::", "using", "fundef", "typedef", "let", "set", "in", "as", "→", "where:", "suchthat:", "end", "{", "}", "all"};

int mpir_lexer_is_keyword(char* lexeme);
int mpir_lexer_process_lexemme(char* lexeme, mpir_lexer* lexer);

#endif
