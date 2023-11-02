/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_lexicalization/mpir_tokeniser.h"

wchar_t* null_terminate_wstring(wchar_t* input)
{
    /* Get the length of the input string */
    size_t length = wcslen(input);

    /* Null-terminate the input wide character string */
    input[length] = L'\0';
    return input;
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
int mpir_tokenise_Qn(mpir_lexer* lexer)
{
    /* Guard clause ensuring the next character is a digit, if not then it's not a numerical literal. */
    if(!(iswdigit(lexer->peek(lexer)))) return ERROR_UNEXPECTED_CHARACTER; else NULL;

    /* Scan and consume the integer values (digits left of decimal point). */
    while (iswdigit(lexer->peek(lexer))) consume_character_any(lexer);

    /* Handle decimal point, if no decimal point then return (./·). */
    if (lexer->peek(lexer) == L'.' || lexer->peek(lexer) == L'·')
    {
        consume_character(lexer, L'.');
    }
    else return mpir_tokenise_process_buffer(lexer, NUMERICAL_LITERAL);

    /* Scan and consume fractional values (digits right of the decimal point). */
    while (iswdigit(lexer->peek(lexer))) consume_character_any(lexer);
    return mpir_tokenise_process_buffer(lexer, NUMERICAL_LITERAL);
}



/**
 * @brief Tokenizes expressions starting with '-' symbol, handling arrow (->) and negative numerical literals.
 *
 * This function checks if the next character in the input stream after '-' represents an arrow symbol or a negative
 * numerical literal. If the next character is '>', it tokenizes "->" as a keyword. If it is a digit, it tokenizes it as
 * a negative numerical literal. If the next character is neither '>', nor a digit, it returns an error.
 *
 * @param lexer A pointer to the lexer structure that provides access to the input stream.
 * @return 0 on success, 1 if a token was not successfully created.
 */
int mpir_tokenise_negative_numerical_or_arrow(mpir_lexer* lexer)
{
    /* Guard clause to ensure the next character is a subtract symbol */
    if (consume_character(lexer, L'-')) NULL; else return 0;

    /* If the next character is a '>', then the symbol is an arrow ( -> ) */
    if (consume_character(lexer, L'>'))
    {
        return mpir_tokenise_process_buffer(lexer, KEYWORD);
    }

    /* If the next character is a digit, then we know it's a negative numerical literal */
    else if(iswdigit(lexer->peek(lexer))) return mpir_tokenise_Qn(lexer);

    /* If it's not a digit or a '>', then it's a syntactic error */
    else return ERROR_UNEXPECTED_CHARACTER;
}



/**
 * @brief Attempts to tokenise a keyword/identifier from the lexers source code.
 *
 * This function examines the characters in the input stream starting from the current position
 * and processes them as an identifier or a keyword until a non-identifiable character is encountered.
 * Identifiable characters are determined using the is_identifiable_character() function.
 *
 * @param lexer A pointer to the lexer structure that provides access to the input stream.
 * @return 0 on failure to tokenise, 1 in the event of a token being successfully created.
 */
int mpir_tokenise_identifiers_and_keywords(mpir_lexer* lexer)
{
    /* Verify the initial character's identity; if non-identifiable, exclude it from consideration. */
    if(is_identifiable_character(lexer->peek(lexer))) NULL; else return 0;

    /* Proceed to scan and consume characters until a non-identifier character is encountered. */
    while(is_identifiable_character(lexer->peek(lexer)))
    {
        consume_character_any(lexer);
    }

    /* Determine the token type based on whether the lexeme matches to a keyword or not. */
    if(is_keyword(lexer->lexeme)) return mpir_tokenise_process_buffer(lexer, KEYWORD);
    else return mpir_tokenise_process_buffer(lexer, IDENTIFIER);
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
        else if(mpir_tokenise_negative_numerical_or_arrow(lxr)) NULL;
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
        else if(mpir_tokenise_identifiers_and_keywords(lxr)) NULL;
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