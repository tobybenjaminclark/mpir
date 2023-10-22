

#ifndef MPIR_COMPILER_MPIR_LEXER_H
#define MPIR_COMPILER_MPIR_LEXER_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BUFFER_SIZE 127
#include "../mpir_token/mpir_token.h"
#include "../../headerbank/mpir_misc/mpir_warnings.h"


/// @brief Struct representing a lexer for tokenizing source code.
///
/// The `mpir_lexication` struct is responsible for maintaining the state of lexical analysis
/// of a source code file. It tracks the current position in the file, the size of the buffer,
/// the number of tokens processed, the current line and column numbers, and other relevant
/// information for tokenization.
///
typedef struct
{
    unsigned long int current_index;    // Current character index
    unsigned long int buffer_size;      // Size of the buffer
    unsigned long int token_count;      // Number of tokens in the list
    unsigned long int line_number;      // Current line number in the source file
    unsigned int column_number;         // Current column number in the source file

    FILE *source_file;                  // Pointer to the open source file
    mpir_token **tokens;                // Current list of tokens
    char current_char;                  // Current character being processed
    char buffer[BUFFER_SIZE];           // Buffer for constructing token lexemes dynamically
} mpir_lexer;



/// @brief Attempts to create a MPIR lexer for tokenizing an .mpir input file.
///
/// This function initializes an MPIR lexer structure used for tokenizing a source file in the MPIR compiler.
/// The lexer processes the specified file, breaking it down into individual tokens that are used in the
/// subsequent stages of the MPIR compilation process. Please free this structure using ther mpir_lexer_free()
/// function after use to avoid memory leaks.
///
/// @param filepath The path to the input file to be tokenized.
///
/// @return A pointer to the newly created MPIR lexer structure, or NULL in case of failure.
///         If memory allocation fails, an error message is logged, and NULL is returned.
///         If the specified file cannot be opened, an error message is logged, the allocated memory is freed, and NULL is returned.
///
mpir_lexer* mpir_lexer_create(const char *filepath);



/// @brief Frees the memory allocated for the given mpir_lexication structure and its associated resources.
///
/// This function deallocates memory used by the provided mpir_lexication structure. It closes the source file,
/// frees the buffer used for constructing token lexemes, and releases memory occupied by individual Token
/// structures in the lexer. Finally, it frees the token array itself and sets the pointer to NULL.
///
/// @param lexer A pointer to the mpir_lexication structure to be deallocated.
///
/// @remark Ensure that the provided mpir_lexication structure is no longer used after calling this function, as
/// accessing the structure or any of its members after deallocation results in undefined behavior, as the
/// structure no longer exists.
///
void mpir_lexer_free(mpir_lexer *lexer);



#endif //MPIR_COMPILER_MPIR_LEXER_H
