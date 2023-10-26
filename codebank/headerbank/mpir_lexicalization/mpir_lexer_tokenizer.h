/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_LEXER_TOKENIZER_H
#define MPIR_COMPILER_MPIR_LEXER_TOKENIZER_H

#include "../../headerbank/mpir_lexicalization/mpir_lexer.h"
#include "../../headerbank/mpir_lexicalization/mpir_lexer_token_handler.h"
#include <ctype.h>
#include <locale.h>
#include <stdio.h>
#include <wchar.h>

#define QUOTE_MARK 39
#define SPEECH_MARK 34

int mpir_lexer_tokenize(mpir_lexer *lexer);
int mpir_lexer_tokenise_unicode();

#endif