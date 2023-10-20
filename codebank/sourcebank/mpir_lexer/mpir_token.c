#include "../../headerbank/mpir_lexer/mpir_token.h"

mpir_token* mpir_create_token(mpir_token_type type, const char lexeme[50], int line)
{
    // Allocate memory for the token structure
    mpir_token* return_token = (mpir_token*)malloc(sizeof(mpir_token));

    // Check if memory allocation was successful
    if (return_token == NULL) {
        // Handle memory allocation failure here (e.g., return an error code)
        return NULL;
    }

    // Copy the lexeme to the token structure (assuming lexeme is a C-style string)
    strncpy(return_token->lexeme, lexeme, sizeof(return_token->lexeme) - 1);

    // Null-terminate the lexeme
    return_token->lexeme[sizeof(return_token->lexeme) - 1] = '\0';

    // Assign values to the token structure
    return_token->type = type;
    return_token->line = line;

    return return_token;
}

void mpir_free_token(mpir_token* token)
{
    free(token);
}