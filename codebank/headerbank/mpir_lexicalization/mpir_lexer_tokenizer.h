#ifndef MPIR_COMPILER_MPIR_LEXER_TOKENIZER_H
#define MPIR_COMPILER_MPIR_LEXER_TOKENIZER_H

#include "../../headerbank/mpir_lexicalization/mpir_lexer.h"
#include "../../headerbank/mpir_lexicalization/mpir_lexer_token_handler.h"
#define QUOTE_MARK 39
#define SPEECH_MARK 34

int mpir_lexer_tokenize(mpir_lexer *lexer);

#endif //MPIR_COMPILER_MPIR_LEXER_TOKENIZER_H
