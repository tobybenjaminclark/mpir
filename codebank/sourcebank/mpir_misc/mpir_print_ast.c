/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_misc/mpir_print_ast.h"

void print_type(struct mpir_ast_type* node, int indentation)
{
    /*
     *  wchar_t data[128];
     */

    (void)wprintf(L"%*ls Type: \n", indentation * TAB_WIDTH, node->data);
    return;
}

void print_types(struct mpir_ast_type** nodes, int indentation)
{
    /* Implement here using print_type */
    return;
}

void print_identifier(struct mpir_ast_identifier* node, int indentation)
{
    /*
     *  wchar_t data[128];
     */

    (void)wprintf(L"%*ls Identifier: \n", indentation * TAB_WIDTH, node->data);
    return;
}

void print_function_declaration(struct mpir_ast_function_declaration* node, int indentation)
{
    /*
    struct mpir_ast_identifier* identifier;
    struct mpir_ast_type** input_types;
    struct mpir_ast_type* return_type;
    struct mpir_command_list* body;
    */
    (void) wprintf(L"%*ls \n", indentation * TAB_WIDTH, "Function Declaration:");
    (void) wprintf(L"%*ls \n", indentation + 1 * TAB_WIDTH, "Function Identifier:");
    (void) print_identifier(node->identifier, indentation + 2);

    (void) wprintf(L"%*ls \n", indentation + 1 * TAB_WIDTH, "Function Return Type:");
    (void) print_type(node->return_type, indentation + 2);

    return;

}