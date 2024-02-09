/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PARSER_WRITER_H
#define MPIR_COMPILER_MPIR_PARSER_WRITER_H

#include "../../headerbank/mpir_parser/mpir_parser.h"
#include "../../headerbank/mpir_wjson/mpir_wjson.h"

int mpir_write_ast(mpir_parser* psr, char path[]);
void mpir_wjsonify_command_list(struct mpir_command_list* body, struct wjson* wjson_list);
#endif