/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_parser/mpir_parse_function_call.h"

/**
 * @brief Parses a Function Call, returns a pointer to a mpir_function_call structure.
 *
 * This function attempts to parse a function call from the provided parser, verifying its structure according to the
 * MPIR grammar. It allocates memory for both the parser, and the input expressions (using the expression parser), the
 * grammar can be seen in the CFG Documentation or as follows: identifier `(` expr0 `,` expr1 `,` ... exprN )
 *
 * @param psr Pointer to the MPIR parser structure.
 * @return A pointer to a dynamically allocated `mpir_function_call` structure representing the parsed function call.
 *         Returns NULL if the parsing fails or encounters an unexpected structure.
 */
struct mpir_function_call* mpir_parse_function_call(mpir_parser* psr)
{
    /* Peek ahead 2 tokens, to ensure it follows IDENTIFIER `(` */
    if(psr->peek(psr)->type != IDENTIFIER) return NULL;
    if(mpir_parser_peek_k(psr, 1)->type != open_bracket) return NULL;

    /* Since we know this is a function call, we can allocate memory */
    struct mpir_function_call* node = malloc(sizeof(struct mpir_function_call));

    /* Parse function identifier */
    wchar_t* identifier;
    if(psr->peek(psr)->type == IDENTIFIER) identifier = parse_function_identifier(psr);
    else return NULL;

    /* Parse `(` */
    if(psr->peek(psr)->type == open_bracket) (void)psr->get(psr);
    else return NULL;

    /* Parse Arguments */
    node->arguments = PARSE_MULTIPLE_STATEMENTS(struct mpir_expression, get_arg, psr);
    if(node->arguments == NULL) return NULL;

    /* Parse `\n` */
    if(psr->peek(psr)->type == NEWLINE) (void)psr->get(psr);
    else return NULL;

    return node;
}