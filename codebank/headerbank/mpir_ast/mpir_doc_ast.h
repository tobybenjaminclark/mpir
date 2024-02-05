/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_DOC_AST_H
#define MPIR_COMPILER_MPIR_DOC_AST_H

/**
 * @struct mpir_ast_doc
 * @brief Represents documentation associated with a variable in the Abstract Syntax Tree (AST).
 *
 * This structure captures information about the documentation of a variable, including its flag type, variable identifier,
 * and an array of documentation lines.
 */
struct mpir_ast_doc
{
    struct mpir_ast_identifier* flag_type;          /** ← Flag type associated with the documentation.           */
    struct mpir_ast_identifier* variable;           /** ← Variable identifier associated with the documentation. */
    wchar_t** documentation;                        /** ← Array of documentation lines.                          */
};

/**
 * @struct mpir_ast_docsection
 * @brief Represents a documentation section in the Abstract Syntax Tree (AST).
 *
 * This structure represents a section of documentation and is part of the AST.
 */
struct mpir_ast_docsection
{
    struct mpir_command_list* docs;                 /** ← Pointer to a list of documentation commands associated with the section. */
};

#endif
