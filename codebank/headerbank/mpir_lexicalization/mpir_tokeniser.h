/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_TOKENISER_H
#define MPIR_COMPILER_MPIR_TOKENISER_H

#include "../../headerbank/mpir_lexicalization/mpir_lexer.h"
#include "../../headerbank/mpir_lexicalization/mpir_lexer_token_handler.h"
#include <ctype.h>
#include <wchar.h>
#include <stdbool.h>
#include <stdarg.h>

#define QUOTE_MARK 39
#define SPEECH_MARK 34

#define ERROR_BUFFER_OVERFLOW 1
#define ERROR_UNEXPECTED_CHARACTER 2

mpir_lexer* mpir_tokenise(const char* file_path);

/**
 * @brief Consumes a character from the source file and appends it to the lexer's buffer.
 *
 * This function verifies if the next character in the input stream matches the expected character. If it does, the
 * function appends the character to the lexer's buffer and increments the current index. If the expected character is
 * not found, an error message is generated and an error code is returned. Additionally, it checks for buffer overflow
 * and handles it by returning an error code if the buffer is full.
 *
 * @param lexer A pointer to the MPIR lexer structure.
 * @param expected_character The character expected to be consumed from the input stream.
 * @return 0 on success, or an error code (ERROR_UNEXPECTED_CHARACTER or ERROR_BUFFER_OVERFLOW) on failure.
 */
int consume_character(mpir_lexer* lexer, wchar_t current_character);

#endif