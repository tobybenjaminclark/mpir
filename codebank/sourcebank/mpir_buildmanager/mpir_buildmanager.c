/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_buildmanager/mpir_buildmanager.h"

int mpir_build(char* input_ast, char* output_file)
{
    // Replace "test.py" with the actual path to your Python script
    const char* pythonScript = "modulebank/mpir_module_python.py";

    // Build the command to run the Python script
    char command[100];
    snprintf(command, sizeof(command), "python3 %s", pythonScript);

    // Use the system function to run the command
    int result = system(command);

    // Check the result of the system call
    if (result == 0) {
        printf("Python script executed successfully.\n");
    } else {
        printf("Error executing Python script.\n");
    }

    return 0;
}