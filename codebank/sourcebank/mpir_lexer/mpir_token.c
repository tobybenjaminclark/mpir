#include "../../headerbank/mpir_lexer/mpir_token.h"



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
mpir_token* mpir_create_token(mpir_token_type type, const char lexeme[50], int line)
{
    // Allocate memory for the token structure & NULL check this (in case of allocation error)
    mpir_token* return_token = (mpir_token*)malloc(sizeof(mpir_token));
    if (return_token == NULL) {return NULL;}

    // Copy the lexeme to the token structure (assuming lexeme is a C-style string)
    strncpy(return_token->lexeme, lexeme, sizeof(return_token->lexeme) - 1);

    // Null-terminate the lexeme
    return_token->lexeme[sizeof(return_token->lexeme) - 1] = '\0';

    // Assign values to the token structure
    return_token->type = type;
    return_token->line_index = line;

    return return_token;
}



/// @brief Frees the allocated memory for a token structure, releasing system resources.
///
/// This function deallocates the memory occupied by a token structure previously created by the
/// mpir_create_token function. In the case of a NULL token being passed, it will do nothing, and
/// simply return.
///
/// @param token A pointer to the token structure that needs to be deallocated.
///
void mpir_free_token(mpir_token* token)
{
    if (token != NULL){free(token);}
    else {return;}
}