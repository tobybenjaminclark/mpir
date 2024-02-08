/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_parser/mpir_parser_writer.h"

#include <stdio.h>

int mpir_write_ast(mpir_parser* psr, char path[])
{
    FILE *file = fopen(path, "w");

    if (file == NULL)
    {
        fprintf(stderr, "Error opening file %s for writing.\n", path);
        return 0; // Return 0 to indicate failure
    }

    fprintf(file, "\nWriting JSON to file.\n");
    printf("\n");

    /* Create wJson node for program */
    struct wjson* wjson_commands = wjson_initialize_list();

    struct mpir_command_node* program_node = psr->program->head;
    while (program_node != NULL)
    {
        switch (program_node->type)
        {
            case FUNCTION_DECLARATION:
                fprintf(file, "FUNCTION_DECLARATION\n");

                struct wjson* wjson_funcdef = wjson_initialize();
                wjson_append_string(wjson_funcdef, L"TYPE", L"FUNCTION_DECLARATION");
                wjson_append_string(wjson_funcdef, L"IDENTIFIER", program_node->data.function_declaration->identifier->data);
                wjson_append_string(wjson_funcdef, L"RETURN_TYPE", program_node->data.function_declaration->return_type->data);

                struct wjson* wjson_funcdef_inputs = wjson_initialize_list();
                int argument_count1 = 0;
                while (program_node->data.function_declaration->inputs[argument_count1] != NULL) {
                    wjson_list_append_string(wjson_funcdef_inputs, program_node->data.function_declaration->inputs[argument_count1]->data);
                    argument_count1++;
                }

                wjson_append_list(wjson_funcdef, L"INPUTS", wjson_funcdef_inputs);
                wjson_list_append_object(wjson_commands, wjson_funcdef);

                break;
            case NEW_TYPE_DECLARATION:
                fprintf(file, "TYPE_DECLARATION\n");
                break;
            default:
                break;
        }
        program_node = program_node->next;
    }

    fclose(file); // Close the file

    struct wjson* wjson_master = wjson_initialize();
    wjson_append_list(wjson_master, L"contents", wjson_commands);
    wjson_print(wjson_master, 0);

    return 1; // Return 1 to indicate success
}