cmake_minimum_required(VERSION 3.26)
project(MPIR_Compiler C)

set(CMAKE_C_STANDARD 23)

add_compile_options(-ansi -Wall)

configure_file(codebank/databank/ascii.txt
        ${CMAKE_CURRENT_BINARY_DIR} COPYONLY)
configure_file(codebank/databank/test.mpir
        ${CMAKE_CURRENT_BINARY_DIR} COPYONLY)
configure_file(codebank/databank/protobuffer_templates/example.protobuf
        ${CMAKE_CURRENT_BINARY_DIR} COPYONLY)

set(SOURCE_FILES
        codebank/sourcebank/main.c
        codebank/sourcebank/mpir_misc/mpir_warnings.c
        codebank/headerbank/mpir_misc/mpir_warnings.h
        codebank/sourcebank/mpir_misc/mpir_help_kernel.c
        codebank/headerbank/mpir_misc/mpir_help_kernel.h
        codebank/sourcebank/mpir_token/mpir_token.c
        codebank/headerbank/mpir_token/mpir_token.h
        codebank/sourcebank/mpir_tokeniser/mpir_lexer.c
        codebank/headerbank/mpir_tokeniser/mpir_lexer.h
        codebank/headerbank/mpir_tokeniser/mpir_lexer_token_handler.h
        codebank/sourcebank/mpir_tokeniser/mpir_tokeniser.c
        codebank/headerbank/mpir_tokeniser/mpir_tokeniser.h
        codebank/sourcebank/mpir_token/mpir_token_create.c
        codebank/headerbank/mpir_token/mpir_token_create.h
        codebank/sourcebank/mpir_token/mpir_token_free.c
        codebank/headerbank/mpir_token/mpir_token_free.h
        codebank/sourcebank/mpir_token/mpir_token_write.c
        codebank/headerbank/mpir_token/mpir_token_write.h
        codebank/sourcebank/mpir_tokeniser/mpir_tokeniser_write.c
        codebank/headerbank/mpir_tokeniser/mpir_tokeniser_write.h
        codebank/sourcebank/mpir_tokeniser/mpir_tokeniser_append.c
        codebank/headerbank/mpir_tokeniser/mpir_tokeniser_append.h
        codebank/sourcebank/mpir_tokeniser/mpir_tokeniser_parse.c
        codebank/headerbank/mpir_tokeniser/mpir_tokeniser_parse.h
        codebank/sourcebank/mpir_protobuffer/mpir_protobuffer.c
        codebank/headerbank/mpir_protobuffer/mpir_protobuffer.h
)

# Create the main executable

add_executable(mpir ${SOURCE_FILES}
        codebank/sourcebank/mpir_protobuffer/mpir_protobuffer.c
        codebank/headerbank/mpir_protobuffer/mpir_protobuffer.h)

enable_testing()
add_executable(mpir_test codebank/testbank/test_example.c
        codebank/testbank/mpir_test_tokenisation.c
        codebank/testbank/mpir_test_tokenisation.h)

add_test(NAME mpir_example_1 COMMAND mpir_test 0)
add_test(NAME tokenisation_test COMMAND mpir_test 1)