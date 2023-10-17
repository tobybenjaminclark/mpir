#include "../headerbank/mpir_misc/mpir_help_kernel.h"
#include <string.h>

int main(int argc, char** argv)
{
    // Iterate through command line arguments
    for (int i = 1; i < argc; i++) {
        // Compare the current argument with the flag you are looking for (e.g., "-h")
        if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
            // If the flag is found, print a help message and exit the program
            mpir_enter_help_kernel();
            return 0;
        }
    }

    return 0;
}
