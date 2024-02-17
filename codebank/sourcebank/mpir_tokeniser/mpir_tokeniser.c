/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_tokeniser/mpir_tokeniser.h"



/**
 * @brief Null-terminates a wide-character string (the lexeme in this use case)
 *
 * This expression takes a wide character string as input and adds a null terminator at the end of the string to ensure it
 * is properly null-terminated. The input string must be allocated with enough memory to accommodate a null terminator.
 *
 * @param input A pointer to the wide character string to be null-terminated.
 * @return A pointer to the null-terminated wide character string.
 *
 * @warning The input string must have enough allocated memory to accommodate the null terminator. Otherwise, this
 * expression may result in undefined behavior by writing beyond the allocated memory.
 */
wchar_t* mpir_terminate_lexeme(wchar_t* input)
{
    /* Get the length of the input string */
    size_t length = wcslen(input);

    /* Null-terminate the input wide character string */
    input[length] = L'\0';
    return input;
}



/**
 * @brief Processes & resets the current lexeme buffer and creates a token of the specified type.
 *
 * This expression creates a token of the given type using the content of the current lexeme buffer. The lexeme buffer is
 * null-terminated, and the token is created with the null-terminated string. The created token is then appended to the
 * lexer's token list, and the lexeme buffer is reset for the next token.
 *
 * @param lexer A pointer to the lexer structure that provides access to the input stream and lexeme buffer.
 * @param toktype The type of the token to be created from the lexeme buffer.
 *
 * @return 1 on success, 0 on failure.
 */
int mpir_tokenise_process_buffer(mpir_lexer *lexer, mpir_token_type toktype)
{
    /* Create a token using the current type and lexeme, note the user must free this after use. */
    mpir_token* token = mpir_create_token(toktype, mpir_terminate_lexeme(lexer->lexeme), 0);
    (void)mpir_lexer_append_token(lexer, token);

    /* Reset the lexeme and it's associated attributes */
    (void)memset(lexer->lexeme, 0, sizeof(wchar_t) * BUFFER_SIZE);
    lexer->buffer_size = 0;
    lexer->current_index = 0;

    return 1;
}



/**
 * @brief Attempts to consume the expected character from the input stream.
 *
 * This expression checks if the next character in the input stream matches the expected character. If the characters
 * match, it consumes the character, appends it to the lexeme, and increments the current index. If the next character
 * does not match the expected character, the expression returns false. If the buffer is full, shows a fatal error.
 *
 * @param lexer A pointer to the lexer structure that provides access to the input stream.
 * @param expected_character The character expected to be present in the input stream.
 *
 * @return True on success, False on failure.
 */
bool mpir_lexer_tryconsume(mpir_lexer* lexer, wchar_t expected_character)
{
    /* Guard Clause ensures the next character is equal to the passed, expected character */
    if (expected_character != lexer->peek(lexer)) return false; else NULL;

    /* Check if lexeme is full, if so, handle accordingly (e.g., resize or process the lexeme) */
    if (lexer->current_index >= BUFFER_SIZE - 1)
    {
        /* Handle lexeme overflow (if it happens). */
        mpir_fatal("mpir_tokeniser: buffer overflow at index (%d).", lexer->current_index);
        return false;
    }

    /* Append the character to the lexeme & increment the current index */
    lexer->lexeme[lexer->current_index] = lexer->get(lexer);
    lexer->current_index++;

    return true;
}


/**
 * @brief Check if a wchar_t is in a list.
 *
 * @param item The wchar_t to search for.
 * @param list Pointer to the array of wchar_t.
 * @param list_size Number of elements in the list.
 * @return 1 if the item is found, 0 otherwise.
 */
int mpir_wchar_in_list(wchar_t item, const wchar_t* list)
{
    while (*list != L'\0')
    {
        if (item == *list) return 1;
        ++list;
    }
    return 0;
}




/**
 * @brief Checks if a given character is an identifiable symbol for creating identifiers.
 *
 * This expression compares the input character with a list of non-identifiable symbols to determine if it is an
 * identifiable symbol using a basic implementation of linear search.
 *
 * @param target The character to be checked for identifiability.
 * @return Returns true if the input character is identifiable, false if it is a non-identifiable symbol.
 */
bool mpir_is_identifiable_char(wchar_t target)
{
    size_t nic_count;     /* ← Stores the total number of non-identifiable symbols.     */
    size_t current_index; /* ← Stores the current index of the non-identifiable symbol. */

    /* Set the NIC list and calculate the length (to iterate over) */
    wchar_t non_identifier_chars[] = DISALLOWED_IDENTIFIER_CHARACTERS;
    nic_count = sizeof(non_identifier_chars) / sizeof(wchar_t);

    /* Iterate through the list, if the target is in the list, return false else return true */
    for (current_index = 0; current_index < nic_count; ++current_index)
    {
        if (non_identifier_chars[current_index] == target) return false;
    }
    return true;
}



/**
 * @brief Checks if a given string matches any keyword in the keyword list.
 *
 * This expression compares the input string with a list of predefined keywords, defined as a macro in the header file.
 * Implements a basic linear search algorithm.
 *
 * @param target The string to be checked against the keyword list.
 * @return Returns true if the input string is a keyword, false otherwise.
 */
int mpir_is_keyword(const wchar_t* target)
{
    size_t keyword_count; /* ← Stores the total number of keywords */
    size_t keyword_index; /* ← Stores the current keyword index    */

    /* Set the keyword list and then calculate the size */
    const wchar_t* keyword_list[] = KEYWORD_LIST;
    keyword_count = sizeof(keyword_list) / sizeof(keyword_list[0]);

    /* Iterate through all keywords, return true if found, false if not. */
    for (keyword_index = 0; keyword_index < keyword_count; ++keyword_index)
    {
        if (wcscmp(target, keyword_list[keyword_index]) == 0) return true;
    }
    return false;
}



/**
 * @brief Consumes the next character in the input stream of the lexer and appends it to the buffer.
 *
 * This expression consumes the next character in the input stream and proxies the call to mpir_lexer_tryconsume expression,
 * anticipating the next character using the lexer->peek(lexer) expression.
 *
 * @param lexer A pointer to the lexer structure that provides access to the input stream.
 * @return true on successful consumption, false on failure.
 */
bool mpir_lexer_consume(mpir_lexer* lexer)
{
    /* Consumes any character, proxys to the mpir_lexer_tryconsume expression */
    return mpir_lexer_tryconsume(lexer, lexer->peek(lexer));
}



/**
 * @brief Tokenizes division operator ('/') and code comments ('//') in the input stream.
 *
 * This expression tokenizes the division operator ('/') and code comments ('//') in the input stream. It checks for the
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
    else return mpir_tokenise_process_buffer(lexer, operator_divide);

    /* If it is a code comment, continue consuming characters until the end of the file or a new line character. */
    while(lexer->peek(lexer) != L'\n' && lexer->peek(lexer) != WEOF)
    {
        if (mpir_lexer_consume(lexer)) continue; else return ERROR_UNEXPECTED_CHARACTER;
    }

    /* Process/Tokenise the buffer as a code comment */
    return mpir_tokenise_process_buffer(lexer, COMMENT);
}



/**
 * @brief Attempts to tokenise string literals ("str" and 'str') from the input stream.
 *
 * This expression tokenizes string literals enclosed in double quotes ("str") or single quotes ('str') in the input
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

    if(lexer->peek(lexer) == L'\'')
    {
        (void)lexer->get(lexer);
        string_literal_terminator = L'\'';
    }
    else if(lexer->peek(lexer) == L'\"')
    {
        (void)lexer->get(lexer);
        string_literal_terminator = L'\"';
    }
    else return 0;

    /* Consume characters while the consumed character is not the string literal termination symbol */
    while(lexer -> peek(lexer) != string_literal_terminator && lexer -> peek(lexer) != WEOF)
    {
        if (mpir_lexer_consume(lexer)) continue; else return 0;
    }

    /* Consume the string literal terminator ("/'), and process the buffer */
    if(lexer->peek(lexer) == string_literal_terminator)
    {
        (void)lexer->get(lexer);
        return mpir_tokenise_process_buffer(lexer, STRING_LITERAL);
    }
    else return ERROR_UNEXPECTED_CHARACTER; /* ← If the string literal is not closed before end of file */
}



/**
 * @brief Attempts to tokenise colon operators (':' and '::') in the input stream.
 *
 * This expression tokenizes the colon operator ':' and the double colon operator '::' in the input stream. It verifies
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
    if (mpir_lexer_tryconsume(lexer, L':')) return mpir_tokenise_process_buffer(lexer, double_colon);
    else return mpir_tokenise_process_buffer(lexer, colon);
}



/**
 * @brief Attempts to tokenise equality operators ('==' and '=' ) in the input stream.
 *
 * This expression tokenizes the equality operators '=='/'=' in the input stream. It verifies the presence of the operator
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
    if(wcscmp(lexer->lexeme, L"=") == 0) return mpir_tokenise_process_buffer(lexer, operator_equals);
    if(wcscmp(lexer->lexeme, L"==") == 0) return mpir_tokenise_process_buffer(lexer, operator_eq);
}



/**
 * @brief Attempst to tokenise boolean comparator operators ('>', '<', '>=', and '<=') in the input stream.
 *
 * This expression tokenizes boolean comparators such as '>', '<', '>=', and '<=' in the input stream. It verifies the
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
    mpir_lexer_consume(lexer);

    /* If the next character is equals consume it, regardless tokenise the buffer */
    (void) mpir_lexer_tryconsume(lexer, '=');
    if(wcscmp(lexer->lexeme, L">") == 0) return mpir_tokenise_process_buffer(lexer, operator_gt);
    if(wcscmp(lexer->lexeme, L">=") == 0) return mpir_tokenise_process_buffer(lexer, operator_gteq);
    if(wcscmp(lexer->lexeme, L"<") == 0) return mpir_tokenise_process_buffer(lexer, operator_lt);
    if(wcscmp(lexer->lexeme, L"<=") == 0) return mpir_tokenise_process_buffer(lexer, operator_lteq);
}



/**
 * @brief Attempts to tokenise negation operators ('!','!=','¬' and '¬=') in the input stream.
 *
 * This expression tokenizes negation operators such as '!', '¬' in the input stream. It verifies the
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

    /* Consume ¬ */
    (void) mpir_lexer_consume(lexer);
    return mpir_tokenise_process_buffer(lexer, operator_not);
}



/**
 * @brief Attempts to tokenise operators (+ - * / ^ ∃ ∀) from the input stream.
 *
 * This expression tokenizes operators such as '+' '/' '-' '*' and '^' in the input stream. It verifies the
 * presence of these operators and consumes the appropriate characters. The negation operators are then tokenized.
 *
 * @param lexer A pointer to the lexer structure that provides access to the input stream.
 * @return 1 on success, 0 on failure.
 */
int mpir_tokenise_operators(mpir_lexer* lexer)
{
    /* Guard Clause to reject if the next character is not a negation. */
    if (mpir_wchar_in_list(lexer->peek(lexer), L"+/*-^∃∀")) NULL;
    else return 0;

    if(mpir_lexer_tryconsume(lexer, L'∃')) return mpir_tokenise_process_buffer(lexer, quantifier_existential);
    if(mpir_lexer_tryconsume(lexer, L'∀')) return mpir_tokenise_process_buffer(lexer, quantifier_universal);

    switch(lexer -> peek(lexer))
    {
        case(L'+'):
            (void) mpir_lexer_tryconsume(lexer, '+');
            return mpir_tokenise_process_buffer(lexer, operator_sum);
        case(L'-'):
            (void) mpir_lexer_tryconsume(lexer, '-');
            return mpir_tokenise_process_buffer(lexer, operator_subtract);
        case(L'/'):
            (void) mpir_lexer_tryconsume(lexer, '/');
            return mpir_tokenise_process_buffer(lexer, operator_divide);
        case(L'*'):
            (void) mpir_lexer_tryconsume(lexer, '*');
            return mpir_tokenise_process_buffer(lexer, operator_multiply);
        case(L'^'):
            (void) mpir_lexer_tryconsume(lexer, '^');
            return mpir_tokenise_process_buffer(lexer, operator_power);
        default:
            return 0;
    }
}



/**
 * @brief Attempts to tokenise brackets/braces ( ) { } from the input stream.
 *
 * This expression tokenizes brackets such as ( ) { } in the input stream. It verifies the
 * presence of the bracket and consumes the appropriate characters. The negation operators are then tokenized.
 *
 * @param lexer A pointer to the lexer structure that provides access to the input stream.
 * @return 1 on success, 0 on failure.
 */
int mpir_tokenise_brackets(mpir_lexer* lexer)
{
    /* Guard Clause to reject if the next character is not a negation. */
    if (mpir_wchar_in_list(lexer->peek(lexer), L"(){}")) NULL;
    else return 0;

    switch(lexer -> peek(lexer))
    {
        case(L'('):
            (void) mpir_lexer_tryconsume(lexer, '(');
            return mpir_tokenise_process_buffer(lexer, open_bracket);
        case(L')'):
            (void) mpir_lexer_tryconsume(lexer, ')');
            return mpir_tokenise_process_buffer(lexer, close_bracket);
        case(L'{'):
            (void) mpir_lexer_tryconsume(lexer, '{');
            return mpir_tokenise_process_buffer(lexer, open_brace);
        case(L'}'):
            (void) mpir_lexer_tryconsume(lexer, '}');
            return mpir_tokenise_process_buffer(lexer, close_brace);
        default:
            return 0;
    }
}



/**
 * @brief Attempts to tokenise boolean connectives from the input stream.
 *∂
 * This expression tokenizes boolean connectives in the input stream. It verifies the
 * presence of the connective and consumes the appropriate characters. The negation operators are then tokenized.
 *
 * @param lexer A pointer to the lexer structure that provides access to the input stream.
 * @return 1 on success, 0 on failure.
 */
int mpir_tokenise_connectives(mpir_lexer* lexer)
{
    /* Guard Clause to reject if the next character is not a negation. */
    if (mpir_wchar_in_list(lexer->peek(lexer), L"→↔^∨")) NULL;
    else return 0;

    if (mpir_lexer_tryconsume(lexer, L'→')) return mpir_tokenise_process_buffer(lexer, operator_arrow);
    if (mpir_lexer_tryconsume(lexer, L'↔')) return mpir_tokenise_process_buffer(lexer, operator_bi_arrow);
    if (mpir_lexer_tryconsume(lexer, L'^')) return mpir_tokenise_process_buffer(lexer, operator_and);
    if (mpir_lexer_tryconsume(lexer, L'∨')) return mpir_tokenise_process_buffer(lexer, operator_or);
}



/**
 * @brief Attempts to tokenise numerical literals e.g. (5, 32.1) in the input stream.
 *
 * This expression processes the input stream as a numerical literal, recognizing both integers and decimals.
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
    while (iswdigit(lexer->peek(lexer))) mpir_lexer_consume(lexer);

    /* Handle decimal point, if no decimal point then return (./·). */
    if (lexer->peek(lexer) == L'.' || lexer->peek(lexer) == L'·')
    {
        mpir_lexer_tryconsume(lexer, L'.');
    }
    else return mpir_tokenise_process_buffer(lexer, NUMERICAL_LITERAL);

    /* Scan and consume fractional values (digits right of the decimal point). */
    while (iswdigit(lexer->peek(lexer))) mpir_lexer_consume(lexer);
    return mpir_tokenise_process_buffer(lexer, NUMERICAL_LITERAL);
}



/**
 * @brief Attempts to tokenise negative numerical literals and arrow symbols (->) in the input stream.
 *
 * This expression checks if the next character in the input stream after '-' represents an arrow symbol or a negative
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
        return mpir_tokenise_process_buffer(lexer, operator_arrow);
    }

    /* If the next character is a digit, then we know it's a negative numerical literal */
    else if(iswdigit(lexer->peek(lexer))) return mpir_tokenise_numerical_literal(lexer);

        /* If it's not a digit or a '>', then it's a syntactic error */
    else return ERROR_UNEXPECTED_CHARACTER;
}



mpir_token_type mpir_match_keyword(wchar_t* lexeme)
{
    if(wcscmp(lexeme, L"using") == 0) return keyword_using;
    else if(wcscmp(lexeme, L"trycast") == 0) return keyword_trycast;
    else if(wcscmp(lexeme, L"into") == 0) return keyword_into;
    else if(wcscmp(lexeme, L"do") == 0) return keyword_do;
    else if(wcscmp(lexeme, L"on") == 0) return keyword_on;
    else if(wcscmp(lexeme, L"where") == 0) return keyword_suchthat;
    else if(wcscmp(lexeme, L"suchthat") == 0) return keyword_suchthat;
    else if(wcscmp(lexeme, L"funcdef") == 0) return keyword_funcdef;
    else if(wcscmp(lexeme, L"typedef") == 0) return keyword_typedef;
    else if(wcscmp(lexeme, L"let") == 0) return keyword_let;
    else if(wcscmp(lexeme, L"set") == 0) return keyword_set;
    else if(wcscmp(lexeme, L"end") == 0) return keyword_end;
    else if(wcscmp(lexeme, L"in") == 0) return keyword_in;
    else if(wcscmp(lexeme, L"as") == 0) return keyword_as;
    else if(wcscmp(lexeme, L",") == 0) return keyword_comma;
    else return 0;
}



/**
 * @brief Attempts to tokenise a keyword/identifier from the input stream.
 *
 * This expression examines the characters in the input stream starting from the current position
 * and processes them as an identifier or a keyword until a non-identifiable character is encountered.
 * Identifiable characters are determined using the mpir_is_identifiable_char() expression.
 *
 * @param lexer A pointer to the lexer structure that provides access to the input stream.
 * @return 0 on failure to tokenise, 1 in the event of a token being successfully created.
 */
int mpir_tokenise_identifiers_and_keywords(mpir_lexer* lexer)
{
    /* Verify the initial character's identity; if non-identifiable, exclude it from consideration. */
    if(mpir_is_identifiable_char(lexer->peek(lexer))) NULL; else return 0;

    /* Proceed to scan and consume characters until a non-identifier character is encountered. */
    while(mpir_is_identifiable_char(lexer->peek(lexer)))
    {
        mpir_lexer_consume(lexer);
    }

    /* Determine the token type based on whether the lexeme matches to a keyword or not. */
    mpir_token_type keyword_type;
    if(( keyword_type = mpir_match_keyword(lexer->lexeme)) != NULL) return mpir_tokenise_process_buffer(lexer, keyword_type);
    else return mpir_tokenise_process_buffer(lexer, IDENTIFIER);
}



int mpir_tokenise_space(mpir_lexer* lexer, int count)
{

    if(lexer->peek(lexer) == L' ')
    {
        (void)mpir_lexer_tryconsume(lexer, L' ');
        if(count == 3)
        {
            (void)mpir_tokenise_process_buffer(lexer, indentation);
            return mpir_tokenise_space(lexer, 0);
        }
        else return mpir_tokenise_space(lexer, count + 1);
    }
    else
    {
        /* Reset the lexeme and it's associated attributes */
        (void)memset(lexer->lexeme, 0, sizeof(wchar_t) * BUFFER_SIZE);
        lexer->buffer_size = 0;
        lexer->current_index = 0;
        return 1;
    }
}



/**
 * @brief Attempts to tokenise MPIR source code from a lexer input stream.
 *
 * This expression tokenizes characters from the given lexer `lxr` based on various rules and states. It handles spaces,
 * newline characters, complex tokenization states for comments, string literals, operators, identifiers, and specials.
 *
 * If a space is detected, it is voided/ignored. If a newline character '\n' is detected, it is tokenized as a newline.
 * Complex tokenization states such ascomments, string literals, operators, and identifiers are handled using specific
 * functions. Unidentifiable characters are tokenized as keywords. If an error occurs during tokenization, the expression
 * returns 0 (Failure). Otherwise, it returns 1 (Success).
 *
 * @param lxr Pointer to the lexer structure containing the input stream.
 * @return 1 on success, 0 on failure.
 */
int mpir_tokenise_base_state(mpir_lexer* lxr)
{
    /* If a space is detected, void/ignore it */
    if (lxr->peek(lxr) == L' ') (void)mpir_tokenise_space(lxr, 0);
    if (mpir_lexer_tryconsume(lxr, L'|')) mpir_tokenise_process_buffer(lxr, pipesymb);

        /* If a newline character \n is detected, tokenise it */
    else if (lxr->peek(lxr) == L'\n')
    {
        mpir_lexer_tryconsume(lxr, L'\n');
        mpir_tokenise_process_buffer(lxr, NEWLINE);
    }

    else if(mpir_lexer_tryconsume(lxr, L',')) mpir_tokenise_process_buffer(lxr, keyword_comma);
    else if(mpir_lexer_tryconsume(lxr, L'\t')) mpir_tokenise_process_buffer(lxr, indentation);

        /* Handle more complex tokenisation states (Token creation is handled in the functions, so do nothing) */
        /* Similar style to alternative parsing, could potentially, add peek() commands here                   */
    else if
            (
            mpir_tokenise_comment_and_division(lxr) ||             /* ← Tokenises '//str' & '/'                */
            mpir_tokenise_string_literal(lxr) ||                   /* ← Tokenises 'str' & "str" literals       */
            mpir_tokenise_colon(lxr) ||                            /* ← Tokenises colon operators ':'/'::'     */
            mpir_tokenise_equality(lxr) ||                         /* ← Tokenises equality operators '='/'=='  */
            mpir_tokenise_comparator(lxr) ||                       /* ← Tokenises '>', '<', '>=', and '<='     */
            mpir_tokenise_negation(lxr) ||                         /* ← Tokenises '!', and '¬'                 */
            mpir_tokenise_connectives(lxr) ||                      /* ← Tokenises boolean comparators          */
            mpir_tokenise_negative_numerical_or_arrow(lxr) ||      /* ← Tokenises negative numericals & '->'   */
            mpir_tokenise_numerical_literal(lxr) ||                /* ← Tokenises numerical literals           */
            mpir_tokenise_brackets(lxr) ||                         /* ← Tokenises brackets/braces              */
            mpir_tokenise_operators(lxr) ||                        /* ← Tokenises + - * / ^ ∀ ∃ operators      */
            mpir_tokenise_identifiers_and_keywords(lxr)            /* ← Tokenises identifiers & keywords       */
            ) NULL;

        /* Handle special symbols */
    else if (!mpir_is_identifiable_char(lxr->peek(lxr)))
    {
        /* Consume character and tokenize as keyword */
        mpir_lexer_consume(lxr);
        mpir_tokenise_process_buffer(lxr, KEYWORD);
    }

        /* Error case, return 0 (Failure), else return 1 (success) */
    else return 0;
    return 1;
}



/* Needs better integration with compiler flags, doxygen not written yet. */
mpir_lexer* mpir_tokenise(const char* file_path, char* output_path)
{
    mpir_lexer *lexer;           /* ← Instance of the lexer we're using, stores all associated data */
    int lexification_fail;      /* ← Becomes 1 if the lexer fails to tokenise something            */

    /* Instantiate a lexer instance, and instruct it to read from the filepath. */
    lexer = mpir_lexer_create(file_path);
    if(lexer == NULL){return 0;}

    /* Tokenise until WEOF is met, then write the tokens to the file if it didn't fail. */
    while (lexer->peek(lexer) != WEOF) if((lexification_fail = !mpir_tokenise_base_state(lexer))) break; else NULL;
    if(!lexification_fail) (void)mpir_tokeniser_write(lexer, output_path);

    return lexer;
}