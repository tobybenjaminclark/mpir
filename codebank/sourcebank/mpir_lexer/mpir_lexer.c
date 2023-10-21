#include "../../headerbank/mpir_lexer/mpir_lexer.h"

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
mpir_lexer* mpir_lexer_create(const char *filepath)
{
    // Allocate memory for the lexer
    mpir_lexer *lexer = (mpir_lexer*)malloc(sizeof(mpir_lexer));

    // Check for memory allocation failure
    if (lexer == NULL)
    {
        mpir_error("Out of memory, failed to allocate MPIR Lexer.");
        return NULL;
    }

    // Initialize lexer properties to their appropriate values.
    lexer->current_index = 0;
    lexer->buffer_size = 0;
    lexer->token_count = 0;
    lexer->line_number = 1;
    lexer->column_number = 1;
    lexer->current_char = '\0';
    lexer->tokens = NULL;

    // Open the source file
    lexer->source_file = fopen(filepath, "r");

    // Check if file opening is successful
    if (lexer->source_file == NULL)
    {
        mpir_error("Lexer failed to open file at %s", filepath);
        free(lexer);
        return NULL;
    }

    return lexer;
}

void mpir_lexer_free(mpir_lexer *lexer)
{
    // Free the buffer used for constructing token lexemes
    fclose(lexer->source_file);

    // Free each token in the list
    for (unsigned long int i = 0; i < lexer->token_count; ++i)
    {
        free(lexer->tokens[i]);
    }

    // Free the list of tokens
    free(lexer->tokens);
    lexer->tokens = NULL;

    // Close the source file
    fclose(lexer->source_file);

    // Free the lexer structure itself
    free(lexer);
}



