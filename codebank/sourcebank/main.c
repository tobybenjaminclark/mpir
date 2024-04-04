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
#include "../headerbank/mpir_buildmanager/mpir_buildmanager.h"

int show_help()
{
    printf("Welcome to the MPIR Compiler use --i to specify input file, --c for config, and --o for output.\n");
}

int show_version()
{
    printf("V1.0\n");
}

int main(int argc, char** argv)
{
    const char* inputFile = NULL;
    const char* outputFile = NULL;
    const char* configFile = NULL;

    // Parse command-line arguments
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-h") == 0){
            show_help();
            exit(0);
        }
        else if (strcmp(argv[i], "-V") == 0){
            show_version();
            exit(0);
        }
        if (strcmp(argv[i], "--i") == 0 && i + 1 < argc) {
            inputFile = argv[i + 1];
            i++;
        } else if (strcmp(argv[i], "--o") == 0 && i + 1 < argc) {
            outputFile = argv[i + 1];
            i++;
        } else if (strcmp(argv[i], "--c") == 0 && i + 1 < argc) {
            configFile = argv[i + 1];
            i++;
        } else {
            printf("Unknown option or missing argument: %s\n", argv[i]);
            return 1; // Exit with error
        }
    }

    // Ensure both input and output files are provided
    if (inputFile == NULL || outputFile == NULL || configFile == NULL) {
        printf("Usage: %s --i <input_file> --o <output_file>\n", argv[0]);
        return 1; // Exit with error
    }

    printf("INPUT FILE  : %s \n", inputFile);
    printf("OUTPUT FILE : %s \n", outputFile);
    printf("CONFIG FILE : %s \n", configFile);

    mpir_lexer* a;
    a = mpir_tokenise(inputFile, "test.md");
    mpir_parser* psr = upgrade_to_parser(a);
    mpir_parse(psr);
    mpir_write_ast(psr, "temp.mpirast");
    mpir_parser_free(psr);

    mpir_build("temp.mpirast", outputFile, configFile, 1);
    return 0;
}

