#include "../headerbank/mpir_misc/mpir_help_kernel.h"
#include "../headerbank/mpir_lexer/mpir_lexer.h"
#include <string.h>

int main(int argc, char** argv)
{
    mpir_lexer* lexer = mpir_lexer_create("test.mpir");
    mpir_lexer_tokenize(lexer);
    mpir_lexer_free(lexer);

    return 0;
}
