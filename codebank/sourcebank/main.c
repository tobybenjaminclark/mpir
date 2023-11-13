/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../headerbank/mpir_tokeniser/mpir_lexer.h"
#include "../headerbank/mpir_tokeniser/mpir_tokeniser.h"
#include "../headerbank/mpir_tokeniser/mpir_tokeniser_write.h"
#include "../headerbank/mpir_tokeniser/mpir_tokeniser_parse.h"
#include "../headerbank/mpir_protobuffer/mpir_protobuffer.h"

int main(int argc, char** argv)
{
    const char* token_names[] = { TOKEN_NAME_MAP };
    int x = 0;
    size_t n = sizeof(token_names)/sizeof(token_names[0]);
    for(x = 0; x < n; x++)
    {
        printf("ID: %d CONTENTS: %s \n", x, token_names[x]);
    }

    int a;
    a = mpir_tokenise("test.mpir");

    (void)parse_tokens_from_json_file("output.txt");
    return 0;
}
