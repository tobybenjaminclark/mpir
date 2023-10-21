#include "../../headerbank/mpir_lexer/mpir_lexer_tokenizer.h"

void mpir_tokenize_divide(mpir_lexer *lexer, int *buffer_index_pointer, char current_character)
{
    int buffer_index = *buffer_index_pointer;

    char second_character;
    char comment_character;
    second_character = fgetc(lexer->source_file);
    lexer->buffer[buffer_index++] = current_character;
    if(second_character == '/')
    {
        lexer->buffer[buffer_index++] = second_character;
        comment_character = fgetc(lexer->source_file);
        while(comment_character != '\n')
        {
            lexer->buffer[buffer_index++] = comment_character;
            comment_character = fgetc(lexer->source_file);
        }
    }
    lexer->buffer[buffer_index] = '\0';
    mpir_lexer_process_lexemme(lexer->buffer);

    lexer->buffer[buffer_index] = '\0';
    memset(lexer->buffer, 0, 80);
    buffer_index = 0;

    *buffer_index_pointer = buffer_index;
    return;
}

void mpir_tokenize_equals(mpir_lexer *lexer, int *buffer_index_pointer, char current_character)
{
    int buffer_index = *buffer_index_pointer;

    char second_character;
    second_character = fgetc(lexer->source_file);
    lexer->buffer[buffer_index++] = current_character;
    if(second_character == '=')
    {
        lexer->buffer[buffer_index++] = second_character;
    }
    else
    {
        ungetc(second_character, lexer->source_file);
    }
    lexer->buffer[buffer_index] = '\0';

    mpir_lexer_process_lexemme(lexer->buffer);

    lexer->buffer[buffer_index] = '\0'; // Null-terminate the buffer
    memset(lexer->buffer, 0, 80);
    buffer_index = 0;

    *buffer_index_pointer = buffer_index;
    return;
}

void mpir_tokenize_subtract(mpir_lexer *lexer, int *buffer_index_pointer, char current_character)
{
    int buffer_index = *buffer_index_pointer;

    char second_character;
    second_character = fgetc(lexer->source_file);
    lexer->buffer[buffer_index++] = current_character;
    if(second_character == '>')
    {
        lexer->buffer[buffer_index++] = second_character;
    }
    lexer->buffer[buffer_index] = '\0';
    mpir_lexer_process_lexemme(lexer->buffer);

    lexer->buffer[buffer_index] = '\0'; // Null-terminate the buffer
    memset(lexer->buffer, 0, 80);
    buffer_index = 0;

    *buffer_index_pointer = buffer_index;
    return;
}

void mpir_tokenize_brace(mpir_lexer *lexer, int *buffer_index_pointer, char current_character)
{
    int buffer_index = *buffer_index_pointer;

    // Process before the comma
    lexer->buffer[buffer_index] = '\0'; // Null-terminate the buffer
    mpir_lexer_process_lexemme(lexer->buffer);
    memset(lexer->buffer, 0, 80);
    buffer_index = 0;

    // Process the comma!
    lexer->buffer[buffer_index++] = current_character;
    lexer->buffer[buffer_index] = '\0'; // Null-terminate the buffer
    mpir_lexer_process_lexemme(lexer->buffer);
    memset(lexer->buffer, 0, 80);
    buffer_index = 0;
    return;
}

void mpir_tokenize_colon(mpir_lexer *lexer, int *buffer_index_pointer, char current_character)
{
    int buffer_index = *buffer_index_pointer;

    char second_character;
    second_character = fgetc(lexer->source_file);
    lexer->buffer[buffer_index++] = current_character;
    if(second_character == ':')
    {
        lexer->buffer[buffer_index++] = second_character;
    }
    else
    {
        ungetc(second_character, lexer->source_file);
    }
    lexer->buffer[buffer_index] = '\0';

    mpir_lexer_process_lexemme(lexer->buffer);

    lexer->buffer[buffer_index] = '\0'; // Null-terminate the buffer
    memset(lexer->buffer, 0, 80);
    buffer_index = 0;

    *buffer_index_pointer = buffer_index;
    return;
}

void mpir_tokenize_pipe(mpir_lexer *lexer, int *buffer_index_pointer, char current_character)
{
    int buffer_index = *buffer_index_pointer;

    // Process before the comma
    lexer->buffer[buffer_index] = '\0'; // Null-terminate the buffer
    mpir_lexer_process_lexemme(lexer->buffer);
    memset(lexer->buffer, 0, 80);
    buffer_index = 0;

    // Process the comma!
    lexer->buffer[buffer_index++] = current_character;
    lexer->buffer[buffer_index] = '\0'; // Null-terminate the buffer
    mpir_lexer_process_lexemme(lexer->buffer);
    memset(lexer->buffer, 0, 80);
    buffer_index = 0;
    return;
}


void mpir_tokenize_comma(mpir_lexer *lexer, int *buffer_index_pointer, char current_character)
{
    int buffer_index = *buffer_index_pointer;

    // Process before the comma
    lexer->buffer[buffer_index] = '\0'; // Null-terminate the buffer
    mpir_lexer_process_lexemme(lexer->buffer);
    memset(lexer->buffer, 0, 80);
    buffer_index = 0;

    // Process the comma!
    lexer->buffer[buffer_index++] = current_character;
    lexer->buffer[buffer_index] = '\0'; // Null-terminate the buffer
    mpir_lexer_process_lexemme(lexer->buffer);
    memset(lexer->buffer, 0, 80);
    buffer_index = 0;
    return;
}


void mpir_tokenize_eol(mpir_lexer *lexer, int *buffer_index_pointer, char current_character)
{
    int buffer_index = *buffer_index_pointer;
    lexer->buffer[buffer_index] = '\0'; // Null-terminate the buffer
    mpir_lexer_process_lexemme(lexer->buffer);
    memset(lexer->buffer, 0, 80);
    buffer_index = 0;

    lexer->buffer[buffer_index++] = current_character;
    mpir_lexer_process_lexemme(lexer->buffer);

    lexer->buffer[buffer_index] = '\0'; // Null-terminate the buffer
    memset(lexer->buffer, 0, 80);
    buffer_index = 0;

    *buffer_index_pointer = buffer_index;
    return;
}

void mpir_tokenize_operator(mpir_lexer *lexer, int *buffer_index_pointer, char current_character)
{
    int buffer_index = *buffer_index_pointer;
    lexer->buffer[buffer_index] = '\0'; // Null-terminate the buffer
    memset(lexer->buffer, 0, 80);
    buffer_index = 0;
    lexer->buffer[buffer_index++] = current_character;
    mpir_lexer_process_lexemme(lexer->buffer);
    lexer->buffer[buffer_index] = '\0'; // Null-terminate the buffer
    memset(lexer->buffer, 0, 80);
    buffer_index = 0;

    *buffer_index_pointer = buffer_index;
    return;
}

void mpir_tokenize_string_literal(mpir_lexer *lexer, int *buffer_index_pointer, char current_character)
{
    int buffer_index = *buffer_index_pointer;
    char inside_string_literal;

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
    *buffer_index_pointer = buffer_index;

    return;
}

void mpir_tokenize_space(mpir_lexer* lexer, int *buffer_index_pointer, char current_character)
{
    int buffer_index = *buffer_index_pointer;
    // Print the token and reset the buffer
    lexer->buffer[buffer_index] = '\0'; // Null-terminate the buffer
    mpir_lexer_process_lexemme(lexer->buffer);
    memset(lexer->buffer, 0, 80);
    buffer_index = 0;

    *buffer_index_pointer = buffer_index;
    return;
}

int mpir_lexer_tokenize(mpir_lexer *lexer)
{
    char current_character = fgetc(lexer->source_file);
    int buffer_index = 0;

    while (current_character != EOF)
    {
        if (current_character == ' ')
        {
            mpir_tokenize_space(lexer, &buffer_index, current_character);
        }
        else if(current_character == '\n')
        {
            mpir_tokenize_eol(lexer, &buffer_index, current_character);
        }
        else if (current_character == '*' || current_character == '+' || current_character == '/' || current_character == '-' || current_character == '='
        || current_character == '^')
        {
            if (current_character == '=')
            {
                mpir_tokenize_equals(lexer, &buffer_index, current_character);
            }
            else if (current_character == '-')
            {
                mpir_tokenize_subtract(lexer, &buffer_index, current_character);
            }
            else if(current_character == '/')
            {
                mpir_tokenize_divide(lexer, &buffer_index, current_character);
            }
            else
            {
                mpir_tokenize_operator(lexer, &buffer_index, current_character);
            }
        }
        else if (current_character == '"' || current_character == "'")
        {
            mpir_tokenize_string_literal(lexer, &buffer_index, current_character);
        }
        else if (current_character == ',')
        {
            mpir_tokenize_comma(lexer, &buffer_index, current_character);
        }
        else if(current_character == ':')
        {
            mpir_tokenize_colon(lexer, &buffer_index, current_character);
        }
        else if(current_character == '{' || current_character == '}')
        {
            mpir_tokenize_brace(lexer, &buffer_index, current_character);
        }
        else if (current_character == '|')
        {
            mpir_tokenize_pipe(lexer, &buffer_index, current_character);
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