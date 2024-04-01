/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../../headerbank/mpir_parser/mpir_func_parsers/mpir_parse_function_call.h"

/**
 * @brief Parses an argument in the context of a expression call, returns a pointer to a mpir_ast_expression structure.
 *
 * This expression parses an argument from the provided parser within the context of a expression call.
 * It checks for the presence of a closing bracket to determine the end of arguments. It parses the expression to
 * the MPIR Grammar spec. Please note that this expression must be freed when after use.
 *
 * @param psr Pointer to the MPIR parser structure.
 * @return A pointer to a dynamically allocated `mpir_ast_expression` structure representing the parsed argument.
 *         Returns NULL if the parsing encounters a closing bracket or fails to parse the argument.
 */
struct mpir_ast_expression* get_arg(mpir_parser* psr)
{
    /* If there is just a closing bracket - we know there are no arguments */
    if(psr->peek(psr)->type == close_bracket) return NULL;

    /* If there isn't then, there should be an expression, we can parse this */
    struct mpir_ast_expression* arg = calloc(1, sizeof (struct mpir_ast_expression));
    arg = mpir_parse_expression(psr, keyword_comma, 0);
    if(psr->peek(psr)->type == keyword_comma) (void)psr->get(psr);
    return arg;
}

/**
 * @brief Parses a Function Call, returns a pointer to a mpir_ast_function_call structure.
 *
 * This expression attempts to parse a expression call from the provided parser, verifying its structure according to the
 * MPIR grammar. It allocates memory for both the parser, and the input expressions (using the expression parser), the
 * grammar can be seen in the CFG Documentation or as follows: identifier `(` expr0 `,` expr1 `,` ... exprN )
 *
 * @param psr Pointer to the MPIR parser structure.
 * @return A pointer to a dynamically allocated `mpir_ast_function_call` structure representing the parsed expression call.
 *         Returns NULL if the parsing fails or encounters an unexpected structure.
 */
struct mpir_ast_function_call* mpir_parse_function_call(mpir_parser* psr)
{
    /* Parse expression identifier */
    struct mpir_ast_identifier* identifier;
    if(psr->peek(psr)->type == IDENTIFIER) identifier = parse_function_identifier(psr);
    else return NULL;

    printf("PARSED FUNCTION CALL!\n");

    /* Parse `(` */
    if(psr->peek(psr)->type == open_bracket) (void)psr->get(psr);
    else return NULL;

    printf("PARSED OPEN BRACKET!\n");

    struct mpir_ast_function_call* node = malloc(sizeof(struct mpir_ast_function_call));
    node->identifier = identifier;

    /* Parse Arguments */
    node->arguments = PARSE_MULTIPLE_STATEMENTS(struct mpir_expression, get_arg, psr);
    if(node->arguments == NULL) return NULL;

    return node;
}