/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_HELP_KERNEL_H
#define MPIR_COMPILER_MPIR_HELP_KERNEL_H

#include "mpir_warnings.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MPIR_LOGO_FILENAME "ascii.txt"
#define HELP_OPTION_1 "[ '1' Project Information ]     "
#define HELP_OPTION_2 "[ '2' I need help ]     "
#define HELP_OPTION_3 "[ '3' Exit Kernel ]"

/// @brief Center Strings and Generate Formatted Output
///
/// This file contains the declaration of the mpir_center_strings function, which takes
/// three input strings and centers them within a fixed-width output string. It calculates
/// the required spacing to center the input strings, concatenates them with even spacing,
/// and returns the resulting centered string. It's used in displaying the help kernel options.
///
/// @param string_one The first input string.
/// @param string_two The second input string.
/// @param string_three The third input string.
/// @return A pointer to a statically allocated centered string.
char* mpir_center_strings(const char* string_one, const char* string_two, const char* string_three);

/// @brief Displays the MPIR Logo in ASCII
///
/// This function is responsible for displaying the logo stored in a file specified
/// by the constant MPIR_LOGO_FILENAME. The logo file is opened and read line by line
/// using a buffer, ensuring that no line in the file exceeds 255 characters.
///
void mpir_display_logo();
void mpir_enter_help_kernel();

#endif //MPIR_COMPILER_MPIR_HELP_KERNEL_H
