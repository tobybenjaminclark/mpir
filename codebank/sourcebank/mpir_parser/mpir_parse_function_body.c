/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_parser/mpir_parse_function_body.h"


struct mpir_on_statement* parse_on_statement(mpir_parser* psr)
{
    /* Parse Indentation then parse `on` keyword */
    while(psr->peek(psr)->type == indentation)(void)psr->get(psr);
    if(psr->peek(psr)->type == keyword_on) (void)psr->get(psr);
    else return NULL;

    /* Parse & discard `on` keyword */
    struct mpir_on_statement* node = calloc(1, sizeof(struct mpir_on_statement));

    printf("PARSED ON!\n102");

    /* Parse literals */
    switch(psr->peek(psr)->type)
    {
        case NUMERICAL_LITERAL:
            node->stored_type = numerical_literal;
            node->literal.mpir_numerical_literal = wcstod(psr->get(psr)->lexeme, NULL);
            break;
        case STRING_LITERAL:
            node->stored_type = string_literal;
            wcscpy(node->literal.mpir_string_literal, psr->get(psr)->lexeme);
            break;
        default:
            return NULL;
    }

    /* Parse & discard arrow */
    if(psr->peek(psr)->type = operator_arrow) (void)psr->get(psr);
    else return NULL;
    printf("PARSED ARROW!\n");
    /* Setup Command List Structure */
    struct mpir_command_list* command;
    command = initialize_command_list();

    /* Parse Command */
    switch(psr->peek(psr)->type)
    {
    case keyword_let:
        parse_let_binding(psr, command);
        break;
    case keyword_set:
        parse_set_binding(psr, command);
        printf("Parsed set binding!");
        break;
        case IDENTIFIER:
        break;
    default:
        /* check for inbuilt call */
        return NULL;
    }

    /* Parse & discard newline */
    if(psr->peek(psr)->type == NEWLINE)(void)psr->get(psr);
    else return NULL;

    node->commands = command;
    return node;
}


struct mpir_on_statement** parse_multiple_on_statements(mpir_parser* psr)
{
    struct mpir_on_statement** nodes = NULL;
    int arg_index = 0;
    struct mpir_on_statement* arg;

    while((arg = parse_on_statement(psr)) != NULL)
    {
        struct mpir_on_statement** temp = realloc(nodes, (arg_index + 2) * sizeof(struct mpir_on_statement*));
        if (temp == NULL)
        {
            free(nodes);
            return NULL;
        }
        nodes = temp;

        nodes[arg_index] = arg;
        arg_index++;
    }
    if(arg_index == 0) return NULL;

    nodes[arg_index] = NULL;
    return nodes;
}


struct mpir_trycast_statement* parse_trycast(mpir_parser* psr, struct mpir_command_list* nodes)
{
    struct mpir_trycast_statement* node = malloc(sizeof (struct mpir_trycast_statement));
    printf("Parsing Trycast!\n");

    /* Parse & Discard `Keyword` Variable */
    if(psr->peek(psr)->type == keyword_trycast) (void)psr->get(psr);
    else return NULL;
    printf("Parsing Trycast!\n");

    /* Parse Dominant Variable */
    node->dominant_variable = parse_identifier(psr);
    if(node->dominant_variable == NULL) return NULL;
    wprintf(L"Parsing Trycast! Dominant Variable -> %ls\n", node->dominant_variable->data);

    /* Parse & Discard `into` keyword */
    if(psr->peek(psr)->type == keyword_into) (void)psr->get(psr);
    else return NULL;
    printf("Parsing Trycast!\n");

    /* Parse 2nd Identifier (casted variable) */
    node->casted_variable = parse_identifier(psr);
    if(node->casted_variable == NULL) return NULL;
    wprintf(L"Parsing Trycast! Casted Variable -> %ls\n", node->casted_variable->data);

    /* Parse `\n` */
    if(psr->peek(psr)->type == NEWLINE) (void)psr->get(psr);
    else return NULL;
    printf("Parsing Trycast!\n");

    /* Parse `on` statements */
    node->actions = parse_multiple_on_statements(psr);
    if(node->actions == NULL) return NULL;
    printf("Parsing Trycast!\n");

    append_command(nodes, (union mpir_command_data){.trycast_statement = node}, TRYCAST_STATEMENT);
    return node;
}


struct mpir_do_statement* parse_do(mpir_parser* psr, struct mpir_command_list* nodes)
{
    struct mpir_do_statement* node = malloc(sizeof (struct mpir_do_statement));

    /* Parse & discard `do` keyword. */
    if(psr->peek(psr)->type == keyword_do) (void)psr->get(psr);
    else return NULL;

    /* Try to parse function call */
    if((node->function = mpir_parse_function_call(psr)) == NULL) return NULL;

    /* Parse & discard newline. */
    if(psr->peek(psr)->type == NEWLINE) (void)psr->get(psr);
    else return NULL;

    /* Parse on statements */
    node->actions = parse_multiple_on_statements(psr);
    if(node->actions == NULL) return NULL;

    append_command(nodes, (union mpir_command_data){.do_statement = node}, DO_STATEMENT);
    return node;
}


struct mpir_command_list* parse_function_body(mpir_parser* psr)
{
    /* Setup & Allocate Memory for Command List */
    char* token_names[] = {TOKEN_NAME_MAP};
    struct mpir_command_list* nodes = initialize_command_list();
    mpir_token_type ntt;

    while ((ntt = psr->peek(psr)->type) != keyword_suchthat)
    {
        wprintf(L"Next Token Type is %s \n", token_names[ntt]);
        switch (ntt)
        {
        case keyword_let:
            parse_let_binding(psr, nodes);
            break;
        case keyword_set:
            parse_set_binding(psr, nodes);
            break;
        case keyword_trycast:
            parse_trycast(psr, nodes);
            break;
        case IDENTIFIER:
            {};
            struct mpir_function_call* a = mpir_parse_function_call(psr);
            if(a != NULL)
            {
                append_command(nodes, (union mpir_command_data){.function_call = a}, FUNCTION_CALL);
            }
            break;
        default:
            (void)psr->get(psr);
        }
    }

    return nodes;
}