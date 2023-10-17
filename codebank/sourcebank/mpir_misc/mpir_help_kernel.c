#include "../../headerbank/mpir_misc/mpir_help_kernel.h"


char* mpir_center_strings(const char* str1, const char* str2, const char* str3)
{
    // Static array to store the centered string
    static char result[121];
    int totalLength = 120;
    int str1Length = strlen(str1);
    int str2Length = strlen(str2);
    int str3Length = strlen(str3);

    int totalChars = str1Length + str2Length + str3Length;
    int spacing = (totalLength - totalChars) / 2;

    // Fill the result string with spaces
    memset(result, ' ', totalLength);

    // Copy the input strings into the result string with even spacing
    strncpy(result + spacing, str1, str1Length);
    strncpy(result + spacing + str1Length, str2, str2Length);
    strncpy(result + spacing + str1Length + str2Length, str3, str3Length);

    // Null-terminate the string
    result[totalLength] = '\0';

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
    printf(mpir_center_strings(HELP_OPTION_1, HELP_OPTION_2, HELP_OPTION_3));
    return;
}