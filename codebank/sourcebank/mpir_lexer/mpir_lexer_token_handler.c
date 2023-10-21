#include "../../headerbank/mpir_lexer/mpir_lexer_token_handler.h"

int mpir_lexer_is_keyword(char* lexeme)
{
    char * x [] = MPIR_KEYWORDS;
    int len = sizeof(x)/sizeof(x[0]);
    int i;

    for(i = 0; i < len; ++i)
    {
        if(!strcmp(x[i], lexeme))
        {
            return 1;
        }
    }
    return 0;
}

int mpir_lexer_is_string_literal(char* lexeme)
{
    if (strlen(lexeme) > 0)
    {
        char first = lexeme[0];
        char last = lexeme[strlen(lexeme) - 1];
        if (first == last && (first == '"' || first == "'"))
        {
            return 1;
        }
    }
    return 0;
}

int mpir_lexer_process_lexemme(char* lexeme)
{
    if (lexeme == NULL || lexeme == "\0" || lexeme == " ")
    {
        printf("Null lexeme\n");
    }

    else if (mpir_lexer_is_keyword(lexeme))
    {
        printf("Keyword! %s\n", lexeme);
    }

    else if (mpir_lexer_is_string_literal(lexeme))
    {
        printf("StrLiteral %s\n", lexeme);
    }

    else
    {
        printf("Other: %s\n", lexeme);
    }

    return 0;
}