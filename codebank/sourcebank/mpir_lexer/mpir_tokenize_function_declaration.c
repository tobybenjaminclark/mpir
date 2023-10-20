#include "../../headerbank/mpir_lexer/mpir_tokenize_function_declaration.h"

bool mpir_consume_char(mpir_lexer* lexer, char expected)
{
    char input_character = fgetc(lexer->source_file);

    if (input_character == expected)
    {
        printf("Character consumed: %c\n", input_character);
        return true;
    }
    else
    {
        mpir_error("Lexer expected '%c' but received '%c' at line %d, column %d", expected, input_character);
        return false;
    }
}

bool mpir_parse_string(mpir_lexer* lexer, const char* str)
{
    int i = 0;
    while (str[i] != '\0')
    {
        if (!mpir_consume_char(lexer, str[i]))
        {
            // Error occurred, handle it (possibly log the error and return false)
            return false;
        }
        i++;
    }
    return true;
}

bool mpir_tokenize_function_declaration(mpir_lexer* lexer)
{
    // Do more stuff here.
    char c;
    c = fgetc(lexer->source_file) != EOF;

    // Detect EOF.
    if(c == NULL)
    {
        mpir_error("Tokenization Error: Expected character, received EOF.");
        return false;
    }
}