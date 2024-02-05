/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_DOC_AST_H
#define MPIR_COMPILER_MPIR_DOC_AST_H

struct mpir_ast_doc
{
    struct mpir_ast_identifier* flag_type;
    struct mpir_ast_identifier* variable;
    wchar_t** documentation;
};

struct mpir_ast_docsection
{
    struct mpir_command_list* docs;
};

#endif
