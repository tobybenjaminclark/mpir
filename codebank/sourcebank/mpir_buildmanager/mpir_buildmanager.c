/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_buildmanager/mpir_buildmanager.h"

int endsWith(const char *str, const char *suffix)
{
    size_t str_len = strlen(str);
    size_t suffix_len = strlen(suffix);

    if (str_len < suffix_len)
        return 0;
    return strcmp(str + str_len - suffix_len, suffix) == 0;
}

int mpir_build(char* input_ast, char* output_file, char* config_file)
{
    int result;
    char command[100];
    if (strcmp(output_file, ".tex")) {
        const char *pythonScript = "codebank/modulebank/mpir_typechecker/typechecker.py";

        // Build the command to run the Python script
        const char *texScript = "codebank/modulebank/mpir_typechecker/typechecker.py";
        printf("python3 %s --i %s --o %s --c %s", texScript, input_ast, output_file, config_file);
        snprintf(command, sizeof(command), "python3 %s --i %s --o %s", texScript, input_ast, output_file);

        // Use the system expression to run the command
        result = system(command);

        // Check the result of the system call
        if (result == 0) {
            printf("Tex script executed successfully.\n");
        } else {
            perror("Error executing Tex script");
        }
    }
    else if(strcmp(output_file, ".py"))
    {
        const char *texScript = "codebank/modulebank/mpir_typechecker/typechecker.py";
        snprintf(command, sizeof(command), "python3 %s --i %s --o %s --c %s", texScript, input_ast, output_file, config_file);
        result = system(command);

        // Check the result of the system call
        if (result == 0) {
            printf("Python script executed successfully.\n");
        } else {
            printf("Error executing Python script.\n");
        }
    }


    return 0;
}