#include <stdio.h>

/// @brief 
/// @return 
FILE* read_file()
{
    // Read the file
    FILE* ptr = fopen("test.txt", "r");
 
    // Check that the file is not null.
    if (NULL == ptr)
    {
        printf("File could not be opened");
    }

    // Return a pointer to the file
    return ptr;
}

/// @brief 
/// @param ptr 
void print_file(FILE* ptr)
{
    // Initialise a character
    char ch;
    
    // Printing what is written in file
    // character by character using loop.
    do {
        ch = fgetc(ptr);
        printf("%c", ch);
 
        // Checking if character is not EOF.
        // If it is EOF stop reading.
    } while (ch != EOF);
 
    // Closing the file
    fclose(ptr);
}

/// @brief 
/// @return 
int main()
{
    FILE* ptr = read_file();
    print_file(ptr);
    return 0;
}