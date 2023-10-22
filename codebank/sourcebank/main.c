#include "../headerbank/mpir_lexer/mpir_lexer.h"
#include "../headerbank/mpir_lexer/mpir_lexer_tokenizer.h"

int main(int argc, char** argv)
{
    mpir_lexer* lexer = mpir_lexer_create("test.mpir");
    mpir_lexer_tokenize(lexer);
    mpir_lexer_free(lexer);

    return 0;
}
