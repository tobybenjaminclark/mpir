/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_LINKED_LIST_H
#define MPIR_COMPILER_MPIR_LINKED_LIST_H

#include <stdio.h>
#include <stdlib.h>
#include "../../headerbank/mpir_ast/mpir_ast.h"

// Define a union for different data types
union command_data {
    struct mpir_function_declaration function_declaration;
    // Add other data types as needed
};

// Define a node structure for the doubly linked list
struct mpir_command_node {
    union command_data data;
    struct mpir_command_node* next;
    struct mpir_command_node* prev;
};

// Define a structure for the doubly linked list
struct mpir_command_list {
    struct mpir_command_node* head;
    struct mpir_command_node* tail;
    int length;
};

void insert_at_end(struct mpir_command_list* list, union command_data data);
struct mpir_command_list* initialize_list();

void insert_at_end(struct mpir_command_list* list, union command_data data);
struct mpir_command_list* initialize_list();

#endif //MPIR_COMPILER_MPIR_LINKED_LIST_H