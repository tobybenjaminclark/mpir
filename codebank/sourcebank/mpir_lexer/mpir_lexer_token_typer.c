#include "../../headerbank/mpir_lexer/mpir_lexer_token_typer.h"

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