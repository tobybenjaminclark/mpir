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

int mpir_lexer_process_lexemme(char* lexemme)
{

    if (mpir_lexer_is_keyword(lexemme))
    {
        printf("Keyword! %s\n", lexemme);
    }

    else
    {
        printf("%s\n", lexemme);
    }

    return 0;
}