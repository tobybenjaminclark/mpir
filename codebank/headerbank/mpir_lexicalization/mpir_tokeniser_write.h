/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_TOKENISER_WRITE_H
#define MPIR_COMPILER_MPIR_TOKENISER_WRITE_H

#include "../../headerbank/mpir_lexicalization/mpir_lexer.h"
#include "../../headerbank/mpir_misc/mpir_warnings.h"
#include "../../headerbank/mpir_token/mpir_token_write.h"

int mpir_tokeniser_write(mpir_lexer* lexer, const char* file_path);

#endif
