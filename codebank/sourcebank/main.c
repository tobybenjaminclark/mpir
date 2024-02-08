/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../headerbank/mpir_architecture/mpir_server.h"
#include "../headerbank/mpir_tokeniser/mpir_lexer.h"
#include "../headerbank/mpir_tokeniser/mpir_tokeniser.h"
#include "../headerbank/mpir_tokeniser/mpir_tokeniser_write.h"
#include "../headerbank/mpir_tokeniser/mpir_tokeniser_parse.h"
#include "../headerbank/mpir_parser/mpir_parser.h"
#include "../headerbank/mpir_parser/mpir_parser_writer.h"
#include "../headerbank/mpir_wjson/mpir_wjson.h"

int main(int argc, char** argv)
{
    mpir_lexer* a;
    a = mpir_tokenise("test.mpir", "test.md");
    mpir_parser* psr = upgrade_to_parser(a);
    mpir_parse(psr);
    mpir_write_ast(psr, "A");
    mpir_parser_free(psr);
    return 0;
}

