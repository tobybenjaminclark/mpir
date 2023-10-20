#ifndef MPIR_COMPILER_MPIR_TOKEN_H
#define MPIR_COMPILER_MPIR_TOKEN_H

#include <string.h>

typedef enum
{
    NUMERICAL_LITERAL,
    OPERATOR,
    IDENTIFIER,
    KEYWORD
} mpir_token_type;

typedef struct
{
    // Type of the token (e.g., number, operator, identifier, etc.)
    mpir_token_type type;

    // Lexeme of the token (actual value as a string)
    char lexeme[50];

    // Line number in the source code where the token appears
    int line;

} mpir_token;


#endif //MPIR_COMPILER_MPIR_TOKEN_H
