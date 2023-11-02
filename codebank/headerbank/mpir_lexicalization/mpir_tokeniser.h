/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_TOKENISER_H
#define MPIR_COMPILER_MPIR_TOKENISER_H

#include "../../headerbank/mpir_lexicalization/mpir_lexer.h"
#include "../../headerbank/mpir_lexicalization/mpir_lexer_token_handler.h"
#include "../../headerbank/mpir_token/mpir_token.h"
#include "../../headerbank/mpir_lexicalization/mpir_tokeniser_write.h"

#include <ctype.h>
#include <wctype.h>
#include <wchar.h>
#include <stdbool.h>
#include <stdarg.h>

#define QUOTE_MARK L'\''
#define SPEECH_MARK L'"'

#define ERROR_BUFFER_OVERFLOW 0
#define ERROR_UNEXPECTED_CHARACTER 0

#define DISALLOWED_IDENTIFIER_CHARACTERS { L'!', L'@', 0x00A3, L'$', L'%', '^', '&', '*', '(', ')','-', '=', '+', \
0x00B1, 0x00A7, '~', '`', '<', '>', ',', '.', '/', '?', ';', ':', '\\', '|', ']', '[', '{', '}', L'"', L'\'', L'\n', \
L'\t', L' ', L'→', L'↔', L'∀', L'∃'}

#define KEYWORD_LIST { L"suchthat", L"where", L"using", L"funcdef", L"typedef", L"let", L"set", L"in", L"as", L"end"}

bool mpir_wchar_in_list(wchar_t target, const wchar_t *list);

int mpir_tokenise_process_buffer(mpir_lexer *lexer, mpir_token_type toktype);

bool mpir_lexer_tryconsume(mpir_lexer* lexer, wchar_t expected_character);

bool is_identifiable_character(wchar_t target);

int is_keyword(const wchar_t* target);

bool consume_character_any(mpir_lexer* lexer);

mpir_lexer* mpir_tokenise(const char* file_path);

/* Tokenises division and comments ( / and //str ) */
int mpir_tokenise_Qc(mpir_lexer* lxr);

/* Tokenises string literals ("str" and 'str') */
int mpir_tokenise_string_literal(mpir_lexer* lexer);

/* Tokenises colon stuff (: and ::) */
int mpir_tokenise_colon(mpir_lexer* lexer);

/* Tokenises equality (= and ==) */
int mpir_tokenise_equality(mpir_lexer* lexer);

/* Tokenises comparison > and < and >= and <= */
int mpir_tokenise_comparator(mpir_lexer* lexer);

/* Tokenises negation (!, !=, ¬ and ¬=) */
int mpir_tokenise_negation(mpir_lexer* lexer);

/* Handles numericals */
int mpir_tokenise_numerical_literal(mpir_lexer* lexer);

int mpir_tokenise_negative_numerical_or_arrow(mpir_lexer* lexer);

int mpir_tokenise_identifiers_and_keywords(mpir_lexer* lexer);

int mpir_tokenise_base_state(mpir_lexer* lxr);

#endif