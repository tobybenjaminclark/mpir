/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_BUILDMANAGER_H
#define MPIR_COMPILER_MPIR_BUILDMANAGER_H

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

int mpir_build(char* input_ast, char* output_file, char* config_file);

#endif
