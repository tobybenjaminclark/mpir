/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../headerbank/mpir_lexicalization/mpir_lexer.h"
#include "../headerbank/mpir_lexicalization/mpir_tokeniser.h"
#include "../headerbank/mpir_lexicalization/mpir_tokeniser_write.h"

int main(int argc, char** argv)
{
    mpir_lexer* lex = mpir_lexer_create("test.mpir");
    if (lex == NULL)
    {
        return 1;
    }
    wchar_t a;
    a = lex->get(lex);
    printf(L"%lc", a);

    while (a != WEOF)
    {
        wprintf(L"%lc", a);
        a = lex->get(lex);
    }
    if(a == WEOF)
    {
        wprintf("End of file!");
    }

    return 0;
}
