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
    /*start_server();*/
    // Create mpir_wjson
    struct mpir_wjson* my_wjson = create_wjson();

    // Add attributes
    wjson_add_attribute(my_wjson, L"name", L"John Doe");
    wjson_add_attribute(my_wjson, L"age", L"25");

    // Create a subjson
    struct mpir_wjson* subjson = create_wjson();
    wjson_add_attribute(subjson, L"city", L"New York");
    wjson_add_attribute(subjson, L"country", L"USA");

    wjson_cre

    // Add subjson to main json
    wjson_add_subwjson(my_wjson, L"address", subjson);

    // Print the created json
    print_wjson(my_wjson, 0);
    write_wjson_to_file("output.wjson", my_wjson, 0);

    // Free the allocated memory
    free_wjson(my_wjson);

    return 0;

    mpir_lexer* a;
    a = mpir_tokenise("test.mpir", "test.md");
    mpir_parser* psr = upgrade_to_parser(a);
    mpir_parse(psr);
    mpir_write_ast(psr, "A");
    mpir_parser_free(psr);
    return 0;
}

