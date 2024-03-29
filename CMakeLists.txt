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
        codebank/sourcebank/mpir_parser/mpir_parser.c
        codebank/headerbank/mpir_parser/mpir_parser.h
        codebank/sourcebank/mpir_ast/mpir_ast.c
        codebank/headerbank/mpir_ast/mpir_ast.h
        codebank/sourcebank/mpir_misc/mpir_linked_list.c
        codebank/headerbank/mpir_misc/mpir_linked_list.h
        codebank/sourcebank/mpir_parser/mpir_parser_utilities.c
        codebank/headerbank/mpir_parser/mpir_parser_utilities.h
        codebank/sourcebank/mpir_parser/mpir_parse.c
        codebank/headerbank/mpir_parser/mpir_parse.h
        codebank/sourcebank/mpir_parser/mpir_func_parsers/mpir_parse_function_header.c
        codebank/headerbank/mpir_parser/mpir_func_parsers/mpir_parse_function_header.h
        codebank/sourcebank/mpir_ast/mpir_command_ast.c
        codebank/headerbank/mpir_ast/mpir_command_ast.h
        codebank/sourcebank/mpir_parser/mpir_func_parsers/mpir_parse_function_body.c
        codebank/headerbank/mpir_parser/mpir_func_parsers/mpir_parse_function_body.h
        codebank/headerbank/mpir_ast/mpir_expression_ast.h
        codebank/sourcebank/mpir_parser/mpir_func_parsers/mpir_parse_expression.c
        codebank/headerbank/mpir_parser/mpir_func_parsers/mpir_parse_expression.h
        codebank/sourcebank/mpir_misc/mpir_print_ast.c
        codebank/headerbank/mpir_misc/mpir_print_ast.h
        codebank/sourcebank/mpir_parser/mpir_func_parsers/mpir_parse_type_header.c
        codebank/headerbank/mpir_parser/mpir_func_parsers/mpir_parse_type_header.h
        codebank/sourcebank/mpir_parser/mpir_func_parsers/mpir_parse_set_binding.c
        codebank/headerbank/mpir_parser/mpir_func_parsers/mpir_parse_set_binding.h
        codebank/sourcebank/mpir_parser/mpir_func_parsers/mpir_parse_let_binding.c
        codebank/headerbank/mpir_parser/mpir_func_parsers/mpir_parse_let_binding.h
        codebank/headerbank/mpir_parser/mpir_parse_multiple.h
        codebank/sourcebank/mpir_parser/mpir_func_parsers/mpir_parse_function_call.c
        codebank/headerbank/mpir_parser/mpir_func_parsers/mpir_parse_function_call.h
        codebank/sourcebank/mpir_parser/mpir_func_parsers/mpir_parse_trycast.c
        codebank/headerbank/mpir_parser/mpir_func_parsers/mpir_parse_trycast.h
        codebank/sourcebank/mpir_parser/mpir_func_parsers/mpir_parse_on.c
        codebank/headerbank/mpir_parser/mpir_func_parsers/mpir_parse_on.h
        codebank/sourcebank/mpir_parser/mpir_func_parsers/mpir_parse_do.c
        codebank/headerbank/mpir_parser/mpir_func_parsers/mpir_parse_do.h
        codebank/sourcebank/mpir_parser/mpir_doc_parsers/mpir_parse_docsection.c
        codebank/headerbank/mpir_parser/mpir_doc_parsers/mpir_parse_docsection.h
        codebank/headerbank/mpir_ast/mpir_doc_ast.h
        codebank/sourcebank/mpir_architecture/mpir_server.c
        codebank/headerbank/mpir_architecture/mpir_server.h
        codebank/sourcebank/mpir_parser/mpir_parser_writer.c
        codebank/headerbank/mpir_parser/mpir_parser_writer.h
        codebank/sourcebank/mpir_wjson/mpir_wjson.c
        codebank/headerbank/mpir_wjson/mpir_wjson.h
        codebank/sourcebank/mpir_parser/mpir_types_parsers/mpir_parse_typedef.c
        codebank/headerbank/mpir_parser/mpir_types_parsers/mpir_parse_typedef.h
        codebank/sourcebank/mpir_parser/mpir_types_parsers/mpir_parse_typelogic.c
        codebank/headerbank/mpir_parser/mpir_types_parsers/mpir_parse_typelogic.h
        codebank/sourcebank/mpir_buildmanager/mpir_buildmanager.c
        codebank/headerbank/mpir_buildmanager/mpir_buildmanager.h
)

# Create the main executable

add_executable(mpir ${SOURCE_FILES})

file(GLOB SOURCE_FILES "codebank/modulebank/*")
foreach(SOURCE_FILE ${SOURCE_FILES})
    get_filename_component(FILE_NAME ${SOURCE_FILE} NAME)
    add_custom_command(
            TARGET mpir POST_BUILD
            COMMAND ${CMAKE_COMMAND} -E copy
            ${SOURCE_FILE}
            ${CMAKE_CURRENT_BINARY_DIR}/modulebank/${FILE_NAME}
    )
endforeach()

enable_testing()
add_executable(mpir_test codebank/testbank/test_example.c
        codebank/testbank/mpir_test_tokenisation.c
        codebank/testbank/mpir_test_tokenisation.h)

add_test(NAME mpir_example_1 COMMAND mpir_test 0)
add_test(NAME tokenisation_test COMMAND mpir_test 1)