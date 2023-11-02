/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_TOKENISER_PARSE_H
#define MPIR_COMPILER_MPIR_TOKENISER_PARSE_H

#include <wchar.h>
#include "../../headerbank/mpir_token/mpir_token.h"

mpir_token** parse_tokens_from_json(const char* json);
mpir_token** parse_tokens_from_json_file(const char* filename);

#endif
