#include "../../headerbank/mpir_lexer/mpir_token.h"

mpir_token* mpir_create_token(mpir_token_type type, char lexeme[50], int line)
{
    mpir_token* return_token;
    return_token->type = type;
    return_token->lexeme = lexeme;
    return_token->line = line;
    return return_token;
}