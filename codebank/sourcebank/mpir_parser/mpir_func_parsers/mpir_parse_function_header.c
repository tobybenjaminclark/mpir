/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../../headerbank/mpir_parser/mpir_func_parsers/mpir_parse_function_header.h"

struct mpir_ast_type** parse_inputs(mpir_parser* psr)
{
    struct mpir_ast_identifier** nodes = NULL;

    int arg_index = 0;
    struct mpir_ast_identifier* arg;
    while((arg = get_type(psr)) != NULL)
    {
        struct mpir_ast_identifier** temp = realloc(nodes, (arg_index + 2) * sizeof(struct mpir_ast_identifier*));
        if (temp == NULL)
        {
            free(nodes);
            return NULL;
        }
        nodes = temp;

        nodes[arg_index] = arg;
        arg_index++;
    }

    nodes[arg_index] = NULL;
    return nodes;
}

/**
 * @brief Function to parse a Function Header, returns a mpir_ast_function_declaration structure.
 *
 * This expression is responsible for parsing the declaration of a expression according to the MPIR Grammar. It gathers
 * the identifier, input types, and output types. Performs memory allocation for the list of input types. The decl.
 * is added to the declaration list in the parser. The grammar can be seen below, and also in the CFG documentation.
 * `funcdef' identifier '::' function_io '\n'`
 *
 * @param psr A pointer to the MPIR parser structure.
 * @return True on parsing success, False on parsing failure.
 */
bool parse_function_declaration(mpir_parser* psr)
{
    char* token_names[] = {TOKEN_NAME_MAP};

    /* Create Funcdef AST node & Consume 'fundef' */
    struct mpir_ast_function_declaration* node = calloc(1, sizeof(struct mpir_ast_function_declaration));
    node->arguments = NULL;

    /* Parse `funcdef */
    if(psr->peek(psr)->type != keyword_funcdef) return false;
    else if(psr->peek(psr)->type == keyword_funcdef) (void)psr->get(psr);
    else return false;

    /* Parse expression identifier */
    if(psr->peek(psr)->type == IDENTIFIER) node->identifier = parse_identifier(psr);
    else return false;
    if(node->identifier == NULL) return false;

    /* Parse I/O shield operator `::` */
    if(psr->peek(psr)->type != double_colon) return false;
    else if(psr->peek(psr)->type == double_colon) (void)psr->get(psr);
    else return false;

    /* Parse I/O Types */
    if(psr->peek(psr)->type != IDENTIFIER)
    {
        fprintf(stderr, "Error: Cannot parse function header on line %d.\n", psr->peek(psr)->line_index);
        fprintf(stderr, "       Expected Input Type Identifier, but got %s!\n", token_names[psr->peek(psr)->type]);
        exit(1);
    }
    if((node->input_types = PARSE_MULTIPLE_STATEMENTS(struct mpir_type , get_type, psr)) == NULL)
    {
        fprintf(stderr, "Error: Cannot parse function header on line %d.\n", psr->peek(psr)->line_index);
        fprintf(stderr, "       Expected Inputs after function-name, but got %s!\n", token_names[psr->peek(psr)->type]);
        exit(1);
    }

    /* Parse Arrow */
    if(!(psr->tryget(psr, operator_arrow)))
    {
        fprintf(stderr, "Error: Cannot parse function header on line %d.\n", psr->peek(psr)->line_index);
        fprintf(stderr, "       Expected ->, but got %s!\n", token_names[psr->peek(psr)->type]);
        exit(1);
    }

    /* Expect Return Type! */
    if(psr->peek(psr)->type == IDENTIFIER) node->return_type = parse_returntype(psr);
    else
    {
        fprintf(stderr, "Error: Cannot parse function header on line %d.\n", psr->peek(psr)->line_index);
        fprintf(stderr, "       Expected Identifier after ->, but got %s!\n", token_names[psr->peek(psr)->type]);
        exit(1);
    }

    /* Parse Newline */
    if(psr->peek(psr)->type == NEWLINE) (void)psr->get(psr);
    else return false;

    /* Parse Funcdef */
    if(psr->peek(psr)->type = keyword_funcdef) (void)psr->get(psr);
    else return false;

    /* Parse Pattern Matching / Inputs */
    mpir_token_type ntt = psr->peek(psr)->type;
    if(ntt == IDENTIFIER && wcscmp(psr->peek(psr)->lexeme, node->identifier) == 0) (void)psr->get(psr);
    else return false;

    if(psr->peek(psr)->type == IDENTIFIER)
    {
        struct mpir_ast_identifier **args = PARSE_MULTIPLE_STATEMENTS(struct mpir_ast_identifier, parse_identifier, psr);
        node->arguments = args;
        while (psr->peek(psr)->type != NEWLINE) (void) psr->get(psr);
    }
    else
    {
        wprintf(L"\n\n%ls\n", psr->peek(psr)->lexeme);
    }

    /* Parse expression body */
    struct mpir_command_list* nodes = initialize_command_list();
    node->body = parse_function_body(psr, nodes);

    /* Parse Doc */
    if(psr->peek(psr)->type == keyword_suchthat)
    {
        /* Consume Suchthat */
        (void)psr->get(psr);
        if(psr->peek(psr)->type == colon) (void)psr->get(psr);
        else return NULL;

        node -> docsection = mpir_parse_docsection(psr);
    }
    else if(psr->peek(psr)->type == keyword_end)
    {
        printf("See END!");
        (void)psr->get(psr);
        node -> docsection = NULL;
    }

    /* Add Declaration Header to Program & Return PSR*/
    append_command(psr->program, (union mpir_command_data){.function_declaration = node}, FUNCTION_DECLARATION);

    return true;
}
