/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_lexicalization/mpir_tokeniser.h"

wchar_t* null_terminate_wstring(const wchar_t* input)
{
    /* Get the length of the input string */
    size_t length = wcslen(input);

    /* Allocate memory for the new wide character string, including space for the null wide character */
    wchar_t* terminated_string = malloc((length + 1) * sizeof(wchar_t));

    /* Check if memory allocation was successful */
    if (terminated_string == NULL) {
        fprintf(stderr, "Memory allocation failed\n");
        exit(EXIT_FAILURE);
    }

    /* Copy the input string to the new memory location */
    wcscpy(terminated_string, input);

    /* Null-terminate the new wide character string */
    terminated_string[length] = L'\0';

    /* Return the null-terminated wide character string */
    return terminated_string;
}

int mpir_tokenise_process_buffer(mpir_lexer *lexer, mpir_token_type toktype)
{
    mpir_token* token = mpir_create_token(toktype, null_terminate_wstring(lexer->lexeme), 0);
    mpir_lexer_append_token(lexer, token);

    memset(lexer->lexeme, 0, sizeof(wchar_t) * BUFFER_SIZE);
    lexer->buffer_size = 0;
    lexer->current_index = 0;

    return 1;
}

/**
 * @brief Consumes a character from the source file and appends it to the lexer's lexeme.
 *
 * This function verifies if the next character in the input stream matches the expected character. If it does, the
 * function appends the character to the lexer's lexeme and increments the current index. If the expected character is
 * not found, an error message is generated and an error code is returned. Additionally, it checks for lexeme overflow
 * and handles it by returning an error code if the lexeme is full.
 *
 * @param lexer A pointer to the MPIR lexer structure.
 * @param expected_character The character expected to be consumed from the input stream.
 * @return 0 on success, or an error code (ERROR_UNEXPECTED_CHARACTER or ERROR_BUFFER_OVERFLOW) on failure.
 */
bool consume_character(mpir_lexer* lexer, wchar_t expected_character)
{

    /* Ensure the expected character is equal to the actual character */
    if (expected_character != lexer->peek(lexer))
    {
        return false;
    }

    /* Check if lexeme is full, if so, handle accordingly (e.g., resize or process the lexeme) */
    if (lexer->current_index >= BUFFER_SIZE - 1)
    {
        /* Handle lexeme overflow (if it happens). */
        fprintf(stderr, "Error: Buffer overflow, index is %ld\n", lexer->current_index);
        return false;
    }

    /* Append the character to the lexeme & increment the current index */
    lexer->lexeme[lexer->current_index] = lexer->get(lexer);
    lexer->current_index++;

    return true;
}

bool is_identifiable_character(wchar_t target)
{
    wchar_t non_identifier_chars[] = DISALLOWED_IDENTIFIER_CHARACTERS;
    size_t nic_count = sizeof(non_identifier_chars) / sizeof(wchar_t);
    size_t current_index;
    for (current_index = 0; current_index < nic_count; ++current_index)
    {
        if (non_identifier_chars[current_index] == target)
        {
            /* Target in list! */
            return false;
        }
    }
    /* Target isn't in the list */
    return true;
}

int is_keyword(const wchar_t* target)
{
    const wchar_t* keyword_list[] = KEYWORD_LIST;
    size_t keyword_count = sizeof(keyword_list) / sizeof(keyword_list[0]);
    size_t keyword_index;
    for (keyword_index = 0; keyword_index < keyword_count; ++keyword_index)
    {
        if (wcscmp(target, keyword_list[keyword_index]) == 0)
        {
            return true;
        }
    }
    return false;
}

bool consume_character_any(mpir_lexer* lexer)
{
    return consume_character(lexer, lexer->peek(lexer));
}

/* Tokenises division and comments ( / and //str ) */
int mpir_tokenise_Qc(mpir_lexer* lxr)
{
    /* Handling Comments */
    if (lxr->peek(lxr) != L'/') return 0;

    if(consume_character(lxr, '/'))
    {
        if (consume_character(lxr, '/'))
        {
            while(lxr->peek(lxr) != L'\n' && lxr->peek(lxr) != WEOF)
            {
                if (consume_character_any(lxr)) continue; else return ERROR_UNEXPECTED_CHARACTER;
            }
            /* Process comment */
            if (consume_character(lxr, '\n')) NULL; else return ERROR_UNEXPECTED_CHARACTER;
            return mpir_tokenise_process_buffer(lxr, COMMENT);
        }
        /* Process operator */
        else return mpir_tokenise_process_buffer(lxr, OPERATOR);
    }
    else return 0;
}

/* Tokenises string literals ("str" and 'str') */
int mpir_tokenise_Qstr(mpir_lexer* lxr)
{
    /* Guard clause */
    if (lxr->peek(lxr) != L'"' && lxr->peek(lxr) != L'\'') return 0;

    /* Discover the string literal terminator */
    wchar_t string_literal_terminator;
    if(lxr->peek(lxr) == L'\'') string_literal_terminator = L'\'';
    else if(lxr->peek(lxr) == L'"') string_literal_terminator = L'"';
    else return ERROR_UNEXPECTED_CHARACTER;

    /* Consume the speech/quote mark! */
    (void) consume_character_any(lxr);

    /* Consume the string literal and produce the token */
    while(lxr -> peek(lxr) != string_literal_terminator && lxr -> peek(lxr) != WEOF)
    {
        if (consume_character_any(lxr)) continue; else return 0;
    }

    if (lxr->peek(lxr) == string_literal_terminator)
    {
        consume_character(lxr, string_literal_terminator);
        return mpir_tokenise_process_buffer(lxr, STRING_LITERAL);
    }
    else return 0;

}

/* Tokenises colon stuff (: and ::) */
int mpir_tokenise_Qco(mpir_lexer* lxr)
{
    if(consume_character(lxr, L':'))
    {
        if(lxr->peek(lxr) == L':')
        {
            consume_character(lxr, L':');
            return mpir_tokenise_process_buffer(lxr, KEYWORD);
        }
        else return mpir_tokenise_process_buffer(lxr, KEYWORD);
    }
    else return 0;
}

/* Tokenises equality (= and ==) */
int mpir_tokenise_Qeq(mpir_lexer* lxr)
{
    if(lxr->peek(lxr) == L'=') NULL;
    else return 0;

    (void)consume_character(lxr, L'=');
    if(lxr->peek(lxr) == L'=')
    {
        consume_character(lxr, L'=');
        return mpir_tokenise_process_buffer(lxr, KEYWORD);
    }
    else return mpir_tokenise_process_buffer(lxr, KEYWORD);
}

/* Tokenises comparison > and < and >= and <= */
int mpir_tokenise_Qcmp(mpir_lexer* lxr)
{
    /* Guard Clause */
    if (lxr->peek(lxr) == L'>' || lxr->peek(lxr) == L'<') NULL;
    else return 0;

    /* Consume boolean comparator */
    consume_character_any(lxr);

    (void)consume_character(lxr, '=');
    return mpir_tokenise_process_buffer(lxr, OPERATOR);
}

/* Tokenises negation (!, !=, ¬ and ¬=) */
int mpir_tokenise_Qneg(mpir_lexer* lxr)
{
    /* Guard Clause */
    if (lxr->peek(lxr) == L'!' || lxr->peek(lxr) == L'¬') NULL;
    else return 0;

    (void)consume_character(lxr, '=');
    return mpir_tokenise_process_buffer(lxr, OPERATOR);
}

/* Handles numericals */
int mpir_tokenise_Qn(mpir_lexer* lxr)
{
    /* Discover and consume digits left of a decimal point */
    if(!(iswdigit(lxr->peek(lxr)))) return ERROR_UNEXPECTED_CHARACTER;
    while (iswdigit(lxr->peek(lxr))) consume_character_any(lxr);

    /* Handle decimal point, if no decimal point then return (./·) */
    if (lxr->peek(lxr) == L'.' || lxr->peek(lxr) == L'·')
    {
        consume_character(lxr, L'.');
    }
    else return mpir_tokenise_process_buffer(lxr, NUMERICAL_LITERAL);

    /* Handle fractional values (digits right of the decimal point */
    while (iswdigit(lxr->peek(lxr))) consume_character_any(lxr);
    return mpir_tokenise_process_buffer(lxr, NUMERICAL_LITERAL);
}

int mpir_tokenise_Qnn(mpir_lexer* lxr)
{
    if (lxr->peek(lxr) != L'-') return 0;

    /* Negation */
    else if (consume_character(lxr, L'-'))
    {
        if (consume_character(lxr, L'>')) return mpir_tokenise_process_buffer(lxr, KEYWORD);
        else if(iswdigit(lxr->peek(lxr))) return mpir_tokenise_Qn(lxr);
        else return ERROR_UNEXPECTED_CHARACTER;
    }
    return ERROR_UNEXPECTED_CHARACTER;
}

int mpir_tokenise_Qi(mpir_lexer* lxr)
{
    /* Consume characters */
    if(is_identifiable_character(lxr->peek(lxr))) NULL;
    else return 0;

    while(is_identifiable_character(lxr->peek(lxr)))
    {
        consume_character_any(lxr);
    }

    /* Match keywords, if not keyword tokenise as identifier */
    if(is_keyword(lxr->lexeme)) return mpir_tokenise_process_buffer(lxr, KEYWORD);
    else return mpir_tokenise_process_buffer(lxr, IDENTIFIER);
}

int mpir_tokenise_base_state(mpir_lexer* lxr)
{
    while(lxr->peek(lxr) != WEOF)
    {
        wprintf(L"Current character is: ' %lc ' \n", lxr->peek(lxr));
        if(mpir_tokenise_Qc(lxr)) NULL;
        else if(mpir_tokenise_Qstr(lxr)) NULL;
        else if(mpir_tokenise_Qco(lxr)) NULL;
        else if(mpir_tokenise_Qeq(lxr)) NULL;
        else if(mpir_tokenise_Qcmp(lxr)) NULL;
        else if(mpir_tokenise_Qneg(lxr)) NULL;
        else if(mpir_tokenise_Qnn(lxr)) NULL;
        else if(lxr->peek(lxr) == L' ') (void)lxr->get(lxr);
        else if(lxr->peek(lxr) == L'\n')
        {
            consume_character(lxr, L'\n');
            mpir_tokenise_process_buffer(lxr, NEWLINE);
        }
        else if(!is_identifiable_character(lxr->peek(lxr)))
        {
            consume_character_any(lxr);
            mpir_tokenise_process_buffer(lxr, KEYWORD);
        }
        else if(mpir_tokenise_Qi(lxr)) NULL;
        else return 1;
    }
    return 0;
}

mpir_lexer* mpir_tokenise(const char* file_path)
{
    mpir_lexer *lexer;          /* ← Instance of the lexer we're using, stores all associated data */

    /* Instantiate a lexer instance, and instruct it to read from the filepath. */
    lexer = mpir_lexer_create(file_path);
    if(lexer == NULL){return NULL;}

    mpir_tokenise_base_state(lexer);
    mpir_tokeniser_write(lexer, "output.txt");

    return lexer;
}