/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_misc/mpir_help_kernel.h"

/** @file
 *  @brief Center Strings and Generate Formatted Output
 *
 *  This file contains the declaration of the mpir_center_strings function, which takes
 *  three input strings and centers them within a fixed-width output string. It calculates
 *  the required spacing to center the input strings, concatenates them with even spacing,
 *  and returns the resulting centered string. It's used in displaying the help kernel options.
 */

/** @brief Center three strings within a fixed-width output string.
 *
 *  This function takes three input strings and centers them within a fixed-width output string.
 *  It calculates the required spacing to center the input strings, concatenates them with even spacing,
 *  and returns the resulting centered string. The returned string is statically allocated.
 *
 *  @param string_one The first input string.
 *  @param string_two The second input string.
 *  @param string_three The third input string.
 *  @return A pointer to a statically allocated centered string. (No need to free!)
 */
char* mpir_center_strings(const char* string_one, const char* string_two, const char* string_three);

/** @brief Displays the MPIR Logo in ASCII
 *
 *  This function is responsible for displaying the logo stored in a file specified
 *  by the constant MPIR_LOGO_FILENAME. The logo file is opened and read line by line
 *  using a buffer, ensuring that no line in the file exceeds 255 characters.
 */
void mpir_display_logo();

/** @brief Enters the MPIR Help Kernel
 *
 *  This function displays the MPIR logo, welcomes the user, and presents the help kernel options.
 */
void mpir_enter_help_kernel();
