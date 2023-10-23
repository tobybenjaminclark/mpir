
// GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark
// This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
// License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.

#include "../headerbank/mpir_lexicalization/mpir_lexer.h"
#include "../headerbank/mpir_lexicalization/mpir_lexer_tokenizer.h"
#include "../headerbank/mpir_lexicalization/mpir_lexer_write_file.h"

int main(int argc, char** argv)
{
    mpir_lexer* lexer = mpir_lexer_create("test.mpir");
    mpir_lexer_tokenize(lexer);

    mpir_lexer_write_file(lexer, "output.mpirtok");

    mpir_lexer_free(lexer);

    return 0;
}
