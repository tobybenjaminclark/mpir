/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_buildmanager/mpir_buildmanager.h"

int mpir_build(char* input_ast, char* output_file)
{
    // Replace "test.py" with the actual path to your Python script
    const char* pythonScript = "mpir_module_tex.py";

    // Build the command to run the Python script
    char command[100];
    snprintf(command, sizeof(command), "python3 %s %s --o %s", pythonScript, input_ast, "documentation.tex");

    // Use the system expression to run the command
    int result = system(command);

    // Check the result of the system call
    if (result == 0) {
        printf("Python script executed successfully.\n");
    } else {
        printf("Error executing Python script.\n");
    }

    // Replace "test.py" with the actual path to your Python script
    const char* texScript = "mpir_module_python.py";
    snprintf(command, sizeof(command), "python3 %s %s --o %s", texScript, input_ast, "python.py");
    result = system(command);

    // Check the result of the system call
    if (result == 0) {
        printf("Python script executed successfully.\n");
    } else {
        printf("Error executing Python script.\n");
    }

    return 0;
}