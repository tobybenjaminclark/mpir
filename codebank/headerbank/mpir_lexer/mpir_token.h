#ifndef MPIR_COMPILER_MPIR_TOKEN_H
#define MPIR_COMPILER_MPIR_TOKEN_H

#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include "../../headerbank/mpir_misc/mpir_warnings.h"


typedef enum
{
    NUMERICAL_LITERAL,
    STRING_LITERAL,
    OPERATOR,
    IDENTIFIER,
    KEYWORD
} mpir_token_type;



typedef struct
{
    // Type of the token (e.g., number, operator, identifier, etc.)
    mpir_token_type type;

    // Lexeme of the token (actual value as a string)
    char lexeme[128];

    // Line number in the source code where the token appears
    unsigned long int line_index;
    unsigned long int column_index;

} mpir_token;



/// @brief Create, allocate & return a new token structure.
///
/// This function allocates memory for a new token structure, initializes its attributes, and returns
/// a pointer to the created token. Tokens are essential elements in the process of lexical analysis
/// (tokenization) within the compiler. They represent identifiable elements in the source code, such
/// as keywords, operators, identifiers, and literals.
///
/// @param type The type of the token, indicating its category (e.g., keyword, identifier, etc.).
/// @param lexeme The lexical representation of the token, typically the characters in the source code.
/// @param line The line number in the source code where the token appears.
///
/// @return A pointer to the newly created token structure, or NULL if memory allocation fails.
///
/// @note The lexeme parameter should be a C-style string (character array) with a maximum length
/// of 50 characters. The lexeme is copied into the token structure, ensuring proper null-termination.
///
/// @warning It is the caller's responsibility to free the allocated memory for the token structure.
///
mpir_token* mpir_create_token(mpir_token_type type, const char lexeme[50], int line);



/// @brief Frees the allocated memory for a token structure, releasing system resources.
///
/// This function deallocates the memory occupied by a token structure previously created by the
/// mpir_create_token function. In the case of a NULL token being passed, it will do nothing, and
/// simply return.
///
/// @param token A pointer to the token structure that needs to be deallocated.
///
void mpir_free_token(mpir_token* token);

#endif //MPIR_COMPILER_MPIR_TOKEN_H
