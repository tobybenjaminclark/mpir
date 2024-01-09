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
    struct mpir_function_declaration function_declaration
};

// Define a node structure for the doubly linked list
struct command_node {
    union command_data data;
    struct command_node* next;
    struct command_node* prev;
};

#endif //MPIR_COMPILER_MPIR_LINKED_LIST_H
