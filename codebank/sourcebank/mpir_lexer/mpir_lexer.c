#include "../../headerbank/mpir_lexer/mpir_lexer.h"

// Function to initialize mpir_lexer struct and open the specified file
mpir_lexer* mpir_lexer_create(const char *filepath)
{
    mpir_lexer *lexer = (mpir_lexer*)malloc(sizeof(mpir_lexer));

    if (lexer == NULL)
    {
        fprintf(stderr, "Memory allocation error\n");
        exit(EXIT_FAILURE);
    }

    lexer->current_index = 0;
    lexer->buffer_size = 0;
    lexer->token_count = 0;
    lexer->line_number = 1;
    lexer->column_number = 1;
    lexer->current_char = '\0';
    lexer->tokens = NULL;

    lexer->source_file = fopen(filepath, "r");

    if (lexer->source_file == NULL)
    {
        fprintf(stderr, "Error opening file: %s\n", filepath);
        free(lexer);
        return(NULL);
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

int mpir_lexer_tokenize(mpir_lexer *lexer)
{
    char current_character = fgetc(lexer->source_file);
    int buffer_index = 0;

    while (current_character != EOF)
    {
        if (current_character == ' ')
        {
            // Print the token and reset the buffer
            lexer->buffer[buffer_index] = '\0'; // Null-terminate the buffer
            printf("token: %s\n", lexer->buffer);
            buffer_index = 0;
        }
        else if (buffer_index < BUFFER_SIZE)
        {
            // Append the current character to the buffer
            lexer->buffer[buffer_index++] = current_character;
        }
        else
        {
            fprintf(stderr, "Token too long: %s\n", lexer->buffer);
            return 1;
        }

        // Read the next character
        current_character = fgetc(lexer->source_file);
    }

    // Print the last token in the buffer if any
    if (buffer_index > 0)
    {
        lexer->buffer[buffer_index] = '\0'; // Null-terminate the buffer
        printf("token: %s\n", lexer->buffer);
    }

    return 0;
}