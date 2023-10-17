
#ifndef MPIR_COMPILER_MPIR_HELP_KERNEL_H
#define MPIR_COMPILER_MPIR_HELP_KERNEL_H

#include "mpir_warnings.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MPIR_LOGO_FILENAME "ascii.txt"
#define HELP_OPTION_1 "[ Information ]     "
#define HELP_OPTION_2 "[ Help ]     "
#define HELP_OPTION_3 "[ Exit ]"

/// @brief Displays the MPIR Logo in ASCII
///
/// This function is responsible for displaying the logo stored in a file specified
/// by the constant MPIR_LOGO_FILENAME. The logo file is opened and read line by line
/// using a buffer, ensuring that no line in the file exceeds 255 characters.
///
void mpir_display_logo();
void mpir_enter_help_kernel();

#endif //MPIR_COMPILER_MPIR_HELP_KERNEL_H
