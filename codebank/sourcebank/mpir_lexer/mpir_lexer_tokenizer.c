#include "../../headerbank/mpir_lexer/mpir_lexer_tokenizer.h"

int mpir_lexer_tokenize(mpir_lexer *lexer)
{
    char current_character = fgetc(lexer->source_file);
    int buffer_index = 0;

    while (current_character != EOF)
    {
        char inside_string_literal;

        if (current_character == ' ')
        {
            // Print the token and reset the buffer
            lexer->buffer[buffer_index] = '\0'; // Null-terminate the buffer
            mpir_lexer_process_lexemme(lexer->buffer);
            memset(lexer->buffer, 0, 80);
            buffer_index = 0;
        }
        else if (current_character == '"' || current_character == "'")
        {
            // Print the token and reset the buffer
            lexer->buffer[buffer_index] = '\0'; // Null-terminate the buffer
            memset(lexer->buffer, 0, 80);
            buffer_index = 0;

            lexer->buffer[buffer_index++] = current_character;
            inside_string_literal = fgetc(lexer->source_file);
            while(inside_string_literal != current_character)
            {
                lexer->buffer[buffer_index++] = inside_string_literal;
                inside_string_literal = fgetc(lexer->source_file);
            }
            lexer->buffer[buffer_index++] = inside_string_literal;
            mpir_lexer_process_lexemme(lexer->buffer);

            memset(lexer->buffer, 0, 80);
            buffer_index = 0;
        }
        else if (buffer_index < BUFFER_SIZE)
        {
            // Append the current character to the buffer
            lexer->buffer[buffer_index++] = current_character;
        }
        else
        {
            mpir_error("Lexer has failed to tokenize '%c', as current token length exceeds allocated buffer (128 characters).");
            fprintf(stderr, "Token too long: %s\n", lexer->buffer);
        }

        // Read the next character
        current_character = fgetc(lexer->source_file);
    }

    // Print the last token in the buffer if any
    if (buffer_index > 0)
    {
        lexer->buffer[buffer_index] = '\0'; // Null-terminate the buffer
        mpir_lexer_process_lexemme(lexer->buffer);
    }

    return 0;
}