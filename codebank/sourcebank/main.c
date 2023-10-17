#include "../headerbank/mpir_symbol_table/mpir_hashmap.h"
#include "../headerbank/mpir_misc/mpir_help_kernel.h"

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

    mpir_hashmap* map = mpir_hashmap_create();

    (void)mpir_hashmap_put_value(map, "key1", "value1");
    (void)mpir_hashmap_put_value(map, "key2", "value2");

    printf("Value for key1: %s\n", mpir_hashmap_get_value(map, "key1")); // Output: value1
    printf("Value for key2: %s\n", mpir_hashmap_get_value(map, "key2")); // Output: value2

    (void)mpir_hashmap_display(map);
    (void)mpir_hashmap_free(map);
    return 0;
}
