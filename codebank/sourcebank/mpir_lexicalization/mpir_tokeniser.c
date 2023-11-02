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
bool mpir_lexer_tryconsume(mpir_lexer* lexer, wchar_t expected_character)
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
    return mpir_lexer_tryconsume(lexer, lexer->peek(lexer));
}



/**
 * @brief Tokenizes division operator ('/') and code comments ('//') in the input stream.
 *
 * This function tokenizes the division operator ('/') and code comments ('//') in the input stream. It checks for the
 * presence of a '/', and if the next character is also '/', it consumes characters until the end of the line or end of
 * file, treating them as a code comment. If the next character is not '/', it tokenizes as division operator.
 *
 * @param lexer A pointer to the lexer structure that provides access to the input stream.
 *
 * @return 1 on success, 0 on failure
 */
int mpir_tokenise_comment_and_division(mpir_lexer* lexer)
{
    /*  Guard clause ensures the next character is a '/', if not then reject */
    if (mpir_lexer_tryconsume(lexer, '/')) NULL;
    else return 0;

    /* If the next character is '/', continue, if not then tokenise as the '/' operator. */
    if (mpir_lexer_tryconsume(lexer, '/')) NULL;
    else return mpir_tokenise_process_buffer(lexer, OPERATOR);

    /* If it is a code comment, continue consuming characters until the end of the file or a new line character. */
    while(lexer->peek(lexer) != L'\n' && lexer->peek(lexer) != WEOF)
    {
        if (consume_character_any(lexer)) continue; else return ERROR_UNEXPECTED_CHARACTER;
    }

    /* Process/Tokenise the buffer as a code comment */
    return mpir_tokenise_process_buffer(lexer, COMMENT);
}



/**
 * @brief Attempts to tokenise string literals ("str" and 'str') from the input stream.
 *
 * This function tokenizes string literals enclosed in double quotes ("str") or single quotes ('str') in the input
 * stream. It identifies the opening quote character, consumes characters until a matching closing quote is found.
 * The characters within the quotes are tokenized as a string literal.
 *
 * @param lexer A pointer to the lexer structure that provides access to the input stream.
 * @return 1 on success, 0 on error.
 */
int mpir_tokenise_string_literal(mpir_lexer* lexer)
{
    /* Guard Clause, try to consume ' and ", remembering if successfully consumed. Else reject */
    wchar_t string_literal_terminator;
    if(mpir_lexer_tryconsume(lexer,  L'\'')) string_literal_terminator = L'\'';
    else if(mpir_lexer_tryconsume(lexer,  L'"')) string_literal_terminator = L'"';
    else return 0;

    /* Consume characters while the consumed character is not the string literal termination symbol */
    while(lexer -> peek(lexer) != string_literal_terminator && lexer -> peek(lexer) != WEOF)
    {
        if (consume_character_any(lexer)) continue; else return 0;
    }

    /* Consume the string literal terminator ("/'), and process the buffer */
    if (mpir_lexer_tryconsume(lexer, string_literal_terminator))
    {
        return mpir_tokenise_process_buffer(lexer, STRING_LITERAL);
    }
    else return ERROR_UNEXPECTED_CHARACTER; /* ← If the string literal is not closed before end of file */
}



/**
 * @brief Attempts to tokenise colon operators (':' and '::') in the input stream.
 *
 * This function tokenizes the colon operator ':' and the double colon operator '::' in the input stream. It verifies
 * the presence of the operator and consumes the appropriate characters. If there are two consecutive colons, they are
 * both consumed and tokenized as a keyword.
 *
 * @param lexer A pointer to the lexer structure that provides access to the input stream.
 * @return 1 on success, 0 on failure.
 */
int mpir_tokenise_colon(mpir_lexer* lexer)
{
    /* Guard clause rejects if the next character is not ':' */
    if(mpir_lexer_tryconsume(lexer, L':')) NULL; else return 0;

    /* If there is another colon, consume it, then tokenise regardless */
    (void) mpir_lexer_tryconsume(lexer, L':');
    return mpir_tokenise_process_buffer(lexer, KEYWORD);
}



/**
 * @brief Attempts to tokenise equality operators ('==' and '=' ) in the input stream.
 *
 * This function tokenizes the equality operators '=='/'=' in the input stream. It verifies the presence of the operator
 * and consumes the appropriate characters. The equality operator is then tokenized as a keyword.
 *
 * @param lexer A pointer to the lexer structure that provides access to the input stream.
 * @return 1 on success, 0 on failure.
 */
int mpir_tokenise_equality(mpir_lexer* lexer)
{
    /* Guard Clause to reject if the next character is not '=' */
    if(mpir_lexer_tryconsume(lexer, L'=')) NULL;
    else return 0;

    /* If the next character is equals, consume it, tokenise regardless */
    (void) mpir_lexer_tryconsume(lexer, L'=');
    return mpir_tokenise_process_buffer(lexer, KEYWORD);
}



/**
 * @brief Attempst to tokenise boolean comparator operators ('>', '<', '>=', and '<=') in the input stream.
 *
 * This function tokenizes boolean comparators such as '>', '<', '>=', and '<=' in the input stream. It verifies the
 * presence of these operators and consumes the appropriate characters. If the next character is '=', it is also
 * consumed and the operator is tokenized. The comparator operators are then tokenized as operators.
 *
 * @param lexer A pointer to the lexer structure that provides access to the input stream.
 * @return 1 on success, 0 on failure.
 */
int mpir_tokenise_comparator(mpir_lexer* lexer)
{
    /* Guard Clause rejects if the next character is not '>' or '<' */
    if (lexer->peek(lexer) == L'>' || lexer->peek(lexer) == L'<') NULL;
    else return 0;

    /* Consume the boolean comparator operator */
    consume_character_any(lexer);

    /* If the next character is equals consume it, regardless tokenise the buffer */
    (void) mpir_lexer_tryconsume(lexer, '=');
    return mpir_tokenise_process_buffer(lexer, OPERATOR);
}



/**
 * @brief Attempts to tokenise negation operators ('!','!=','¬' and '¬=') in the input stream.
 *
 * This function tokenizes negation operators such as '!', '!=', '¬', and '¬=' in the input stream. It verifies the
 * presence of these operators and consumes the appropriate characters. The negation operators are then tokenized.
 *
 * @param lexer A pointer to the lexer structure that provides access to the input stream.
 * @return 1 on success, 0 on failure.
 */
int mpir_tokenise_negation(mpir_lexer* lexer)
{
    /* Guard Clause to reject if the next character is not a negation. */
    if (lexer->peek(lexer) == L'!' || lexer->peek(lexer) == L'¬') NULL;
    else return 0;

    /* If the next character is an equal sign, then consume it, tokenise as operator regardless. */
    (void) mpir_lexer_tryconsume(lexer, '=');
    return mpir_tokenise_process_buffer(lexer, OPERATOR);
}



/**
 * @brief Attempts to tokenise numerical literals e.g. (5, 32.1) in the input stream.
 *
 * This function processes the input stream as a numerical literal, recognizing both integers and decimals.
 * It checks for a sequence of digits representing the integral part, followed by an optional decimal point ('.' or '·'),
 * and then scans for digits representing the fractional part.
 *
 * @param lexer A pointer to the lexer structure that provides access to the input stream.
 *
 * @return 1 on success, 0 or an error on failure.
 */
int mpir_tokenise_numerical_literal(mpir_lexer* lexer)
{
    /* Guard clause ensuring the next character is a digit, if not then it's not a numerical literal. */
    if(!(iswdigit(lexer->peek(lexer)))) return ERROR_UNEXPECTED_CHARACTER; else NULL;

    /* Scan and consume the integer values (digits left of decimal point). */
    while (iswdigit(lexer->peek(lexer))) consume_character_any(lexer);

    /* Handle decimal point, if no decimal point then return (./·). */
    if (lexer->peek(lexer) == L'.' || lexer->peek(lexer) == L'·')
    {
        mpir_lexer_tryconsume(lexer, L'.');
    }
    else return mpir_tokenise_process_buffer(lexer, NUMERICAL_LITERAL);

    /* Scan and consume fractional values (digits right of the decimal point). */
    while (iswdigit(lexer->peek(lexer))) consume_character_any(lexer);
    return mpir_tokenise_process_buffer(lexer, NUMERICAL_LITERAL);
}



/**
 * @brief Attempts to tokenise negative numerical literals and arrow symbols (->) in the input stream.
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
    if (mpir_lexer_tryconsume(lexer, L'-')) NULL; else return 0;

    /* If the next character is a '>', then the symbol is an arrow ( -> ) */
    if (mpir_lexer_tryconsume(lexer, L'>'))
    {
        return mpir_tokenise_process_buffer(lexer, KEYWORD);
    }

    /* If the next character is a digit, then we know it's a negative numerical literal */
    else if(iswdigit(lexer->peek(lexer))) return mpir_tokenise_numerical_literal(lexer);

    /* If it's not a digit or a '>', then it's a syntactic error */
    else return ERROR_UNEXPECTED_CHARACTER;
}



/**
 * @brief Attempts to tokenise a keyword/identifier from the input stream.
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
        if(mpir_tokenise_comment_and_division(lxr)) NULL;
        else if(mpir_tokenise_string_literal(lxr)) NULL;
        else if(mpir_tokenise_colon(lxr)) NULL;
        else if(mpir_tokenise_equality(lxr)) NULL;
        else if(mpir_tokenise_comparator(lxr)) NULL;
        else if(mpir_tokenise_negation(lxr)) NULL;
        else if(mpir_tokenise_negative_numerical_or_arrow(lxr)) NULL;
        else if(lxr->peek(lxr) == L' ') (void)lxr->get(lxr);
        else if(lxr->peek(lxr) == L'\n')
        {
            mpir_lexer_tryconsume(lxr, L'\n');
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