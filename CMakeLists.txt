cmake_minimum_required(VERSION 3.26)
project(MPIR_Compiler C)

set(CMAKE_C_STANDARD 23)

configure_file(codebank/databank/ascii.txt
        ${CMAKE_CURRENT_BINARY_DIR} COPYONLY)

add_compile_options(-ansi)

add_executable(mpir codebank/sourcebank/main.c
        codebank/sourcebank/mpir_symbol_table/mpir_hashmap.c
        codebank/headerbank/mpir_symbol_table/mpir_hashmap.h
        codebank/sourcebank/mpir_misc/mpir_warnings.c
        codebank/headerbank/mpir_misc/mpir_warnings.h
        codebank/sourcebank/mpir_misc/mpir_help_kernel.c
        codebank/headerbank/mpir_misc/mpir_help_kernel.h)
