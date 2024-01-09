/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_DEFINITION_LIST_H
#define MPIR_COMPILER_MPIR_DEFINITION_LIST_H

#include "../../headerbank/mpir_ast/mpir_ast.h"

union mpir_declaration_data {
    struct mpir_function_declaration function_declaration;
};

struct mpir_declaration_node {
    union mpir_declaration_data data;
    struct mpir_declaration_node* next;
    struct mpir_declaration_node* prev;
};

struct mpir_declaration_list {
    struct mpir_declaration_node* head;
    struct mpir_declaration_node* tail;
    int length;
};

struct mpir_declaration_node* create_declaration_node(union mpir_declaration_data data);
struct mpir_declaration_list* initialize_declaration_list();
void add_declaration(struct mpir_declaration_list* list, union mpir_declaration_data data);
void free_list(struct mpir_command_list* list);

#endif
