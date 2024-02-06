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

    struct mpir_command_node* program_node = psr->program->head;
    while (program_node != NULL)
    {
        switch (program_node->type)
        {
            case FUNCTION_DECLARATION:
                fprintf(file, "FUNCTION_DECLARATION\n");
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

    return 1; // Return 1 to indicate success
}