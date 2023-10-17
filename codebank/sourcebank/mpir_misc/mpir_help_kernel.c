#include "../../headerbank/mpir_misc/mpir_help_kernel.h"

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
char* mpir_center_strings(const char* string_one, const char* string_two, const char* string_three)
{
    // Static array to store the centered string_three
    static char result[121];
    int total_length = 120;

    int string_one_length = strlen(string_one);
    int string_two_length = strlen(string_two);
    int string_three_length = strlen(string_three);

    int accumulative_string_length = string_one_length + string_two_length + string_three_length;
    int spacing = (total_length - accumulative_string_length) / 2;

    // Fill the result string_three with spaces
    memset(result, ' ', total_length);

    // Copy the input strings into the result string_three with even spacing
    strncpy(result + spacing, string_one, string_one_length);
    strncpy(result + spacing + string_one_length, string_two, string_two_length);
    strncpy(result + spacing + string_one_length + string_two_length, string_three, string_three_length);

    // Null-terminate the string_three
    result[total_length] = '\n';

    return result;
}


/// @brief Displays the MPIR Logo in ASCII
///
/// This function is responsible for displaying the logo stored in a file specified
/// by the constant MPIR_LOGO_FILENAME. The logo file is opened and read line by line
/// using a buffer, ensuring that no line in the file exceeds 255 characters.
void mpir_display_logo()
{
    // Declare variables to open the file, and a buffer to read from it.
    // The buffer assumes no line in the file exceeds 255 characters.
    FILE *file = NULL;
    char line[256];

    // Open the file & perform a NULL check.
    file = fopen(MPIR_LOGO_FILENAME, "r");
    if (file == NULL)
    {
        mpir_error("mpir_help_kernel.c : unable to display logo at %s", MPIR_LOGO_FILENAME);
        return;
    }

    // Read and display lines until the end of the file
    while (fgets(line, sizeof(line), file) != NULL)
    {
        printf("%s", line);
    }

    // Close the file & return
    fclose(file);
    return;
}


void mpir_enter_help_kernel()
{
    // Show the logo.
    (void)mpir_display_logo();

    // Display some info.
    printf("%s", mpir_center_strings("", "Welcome to MPIR Kernel, Your digital assistant in compilation! :)", ""));
    printf("%s", mpir_center_strings(HELP_OPTION_1, HELP_OPTION_2, HELP_OPTION_3));
    return;
}