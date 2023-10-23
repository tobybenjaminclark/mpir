
// GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark
// This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
// License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.

#include <stdlib.h>

int main(int argc, char *argv[])
{
    if (argc < 2) {
        // Check if there are enough arguments
        return 1;
    }

    // Convert the first command-line argument to an integer
    int number = atoi(argv[1]);

    return number;
}