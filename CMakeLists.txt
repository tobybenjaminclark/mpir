cmake_minimum_required(VERSION 3.26)
project(MPIR_Compiler C)

set(CMAKE_C_STANDARD 23)

configure_file(codebank/databank/ascii.txt
        ${CMAKE_CURRENT_BINARY_DIR} COPYONLY)
configure_file(codebank/databank/test.mpir
        ${CMAKE_CURRENT_BINARY_DIR} COPYONLY)


add_executable(mpir codebank/sourcebank/main.c
        codebank/sourcebank/mpir_symbol_table/mpir_hashmap.c
        codebank/headerbank/mpir_symbol_table/mpir_hashmap.h
        codebank/sourcebank/mpir_misc/mpir_warnings.c
        codebank/headerbank/mpir_misc/mpir_warnings.h
        codebank/sourcebank/mpir_misc/mpir_help_kernel.c
        codebank/headerbank/mpir_misc/mpir_help_kernel.h
        codebank/sourcebank/mpir_token/mpir_token.c
        codebank/headerbank/mpir_token/mpir_token.h
        codebank/sourcebank/mpir_lexicalization/mpir_lexer.c
        codebank/headerbank/mpir_lexicalization/mpir_lexer.h
        codebank/sourcebank/mpir_lexicalization/mpir_lexer_token_handler.c
        codebank/headerbank/mpir_lexicalization/mpir_lexer_token_handler.h
        codebank/sourcebank/mpir_lexicalization/mpir_lexer_tokenizer.c
        codebank/headerbank/mpir_lexicalization/mpir_lexer_tokenizer.h
        codebank/sourcebank/mpir_token/mpir_token_create.c
        codebank/headerbank/mpir_token/mpir_token_create.h
        codebank/sourcebank/mpir_token/mpir_token_free.c
        codebank/headerbank/mpir_token/mpir_token_free.h
        codebank/sourcebank/mpir_token/mpir_token_write.c
        codebank/headerbank/mpir_token/mpir_token_write.h
        codebank/sourcebank/mpir_lexicalization/mpir_lexer_write_file.c
        codebank/headerbank/mpir_lexicalization/mpir_lexer_write_file.h
        codebank/sourcebank/mpir_lexicalization/mpir_lexer_add_token.c
        codebank/headerbank/mpir_lexicalization/mpir_lexer_add_token.h
)
