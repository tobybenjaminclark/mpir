/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_buildmanager/mpir_buildmanager.h"

int mpir_build(char* input_ast, char* output_file, char* config_file, int weaveortangle)
{
    int result;
    char command[100];
    if(weaveortangle == 2) {
        const char *pythonScript = "codebank/modulebank/mpir_module_tex.py";

        // Build the command to run the Python script
        snprintf(command, sizeof(command), "python3 %s %s --o %s --c %s", pythonScript, input_ast, config_file, "documentation.tex");

        // Use the system expression to run the command
        result = system(command);

        // Check the result of the system call
        if (result == 0) {
            printf("Python script executed successfully.\n");
        } else {
            printf("Error executing Python script.\n");
        }
    }
    else {
        const char *texScript = "codebank/modulebank/mpir_typechecker/typechecker.py";
        snprintf(command, sizeof(command), "python3 %s --i %s --o %s --c %s", texScript, input_ast, config_file, "python.py");
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