#include "../../headerbank/mpir_lexer/mpir_tokenize_function_declaration.h"

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