
// GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark
// This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
// License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.

#ifndef MPIR_COMPILER_MPIR_LEXER_TOKEN_HANDLER_H
#define MPIR_COMPILER_MPIR_LEXER_TOKEN_HANDLER_H

#include <stdio.h>
#include <string.h>
#include <wchar.h>

#define MPIR_KEYWORDS {"->", "::", "using", "fundef", "typedef", "let", "set", "in", "as", "→", "where:", "suchthat:", "end", "{", "}", "all"};

int mpir_lexer_is_keyword(char* lexeme);
int mpir_lexer_process_lexemme(char* lexeme);

#endif //MPIR_COMPILER_MPIR_LEXER_TOKEN_HANDLER_H