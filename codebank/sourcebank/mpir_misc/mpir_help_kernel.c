#include "../../headerbank/mpir_misc/mpir_help_kernel.h"

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
    printf("Displaying MPIR Compilation System Flags.\n");
    printf("\t\t-h/--help\t\t-\t Interactive Help Kernel for the MPIR Compilation System.\n");
    printf("\t\t-v/--verbose\t-\t Runs the MPIR Compilation System in Verbose Mode.\n");
    return;
}