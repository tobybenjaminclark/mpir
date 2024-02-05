/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_LINKED_LIST_H
#define MPIR_COMPILER_MPIR_LINKED_LIST_H

#include <stdio.h>
#include <stdlib.h>
#include "../../headerbank/mpir_ast/mpir_command_ast.h"


union mpir_command_data {
    struct mpir_ast_function_call* function_call;
    struct mpir_ast_function_declaration* function_declaration;
    struct mpir_ast_type_declaration* type_declaration;
    struct mpir_ast_type_assignment* type_assignment;
    struct mpir_ast_value_assignment* value_assignment;
    struct mpir_ast_trycast_statement* trycast_statement;
    struct mpir_ast_do_statement* do_statement;
    struct mpir_ast_doc* doc_statement;
};

enum mpir_command_type{
    TYPE_DECLARATION,
    FUNCTION_CALL,
    FUNCTION_DECLARATION,
    TYPE_ASSIGNMENT,
    VALUE_ASSIGNMENT,
    TRYCAST_STATEMENT,
    DO_STATEMENT,
    DOC_STATEMENT,
    NEW_TYPE_DECLARATION,
};

struct mpir_command_node {
    union mpir_command_data data;
    enum mpir_command_type type;
    struct mpir_command_node* next;
    struct mpir_command_node* prev;
};

struct mpir_command_list {
    struct mpir_command_node* head;
    struct mpir_command_node* tail;
    int length;
};

void append_command(struct mpir_command_list* list, union mpir_command_data data, enum mpir_command_type type);
struct mpir_command_list* initialize_command_list();

#endif
