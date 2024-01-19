/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_parser/mpir_parse_function_body.h"


/**
 * @brief Function to parse a 'let' binding (type assignment) within the MPIR parser.
 *
 * This function parses a 'let' binding within the context of MPIR. A 'let' binding involves declaring a variable
 * with a specified type. The function sequentially parses the 'let' keyword, the variable identifier, the 'as' keyword,
 * and the associated type identifier. It then creates and returns a dynamically allocated `struct mpir_type_assignment`
 * representing the parsed 'let' binding as part of the AST.
 *
 * @param psr A pointer to the MPIR parser structure.
 *
 * @return A pointer to a dynamically allocated `struct mpir_type_assignment` on successful parsing.
 */
struct mpir_type_assignment* parse_let_binding(mpir_parser* psr, struct mpir_command_list* nodes)
{
    struct mpir_type_assignment* node = malloc(sizeof(struct mpir_type_assignment));

    /* Parse `let` */
    if(psr->peek(psr)->type == keyword_let) (void)psr->get(psr);
    else return NULL;

    /* Parse variable identifier */
    if(psr->peek(psr)->type == IDENTIFIER) wcscpy(node->identifier, (psr->get(psr))->lexeme);
    else return NULL;
    if(node->identifier == NULL) return NULL;

    /* Parse `as` */
    if(psr->peek(psr)->type == keyword_as) (void)psr->get(psr);
    else return NULL;

    /* Parse type identifier */
    if(psr->peek(psr)->type == IDENTIFIER) wcscpy(node->type, (psr->get(psr))->lexeme);
    else return NULL;
    if(node->type == NULL) return NULL;



    append_command(nodes, (union mpir_command_data){.type_assignment = node}, TYPE_ASSIGNMENT);

    return node;
}


/**
 * @brief Function to parse a 'set' binding (value assignment) within the MPIR parser.
 *
 * This function parses a 'set' binding within the context of the MPIR. A 'set' binding involves assigning a value to a
 * variable with a specified type. The function sequentially parses the 'set' keyword, the variable identifier, the 'as'
 * keyword, and the associated expression (value). It then creates and returns a dynamically allocated
 * `struct mpir_value_assignment` representing the parsed 'set' binding.
 *
 * @param psr A pointer to the MPIR parser structure.
 * @return A pointer to a dynamically allocated `struct mpir_value_assignment` on successful parsing.
 */
struct mpir_value_assignment* parse_set_binding(mpir_parser* psr, struct mpir_command_list* nodes)
{
    struct mpir_value_assignment* node = calloc(1, sizeof(struct mpir_value_assignment));

    /* Parse `set` */
    if(psr->peek(psr)->type == keyword_set) (void)psr->get(psr);
    else return NULL;

    /* Parse variable identifier */
    if(psr->peek(psr)->type == IDENTIFIER) wcscpy(node->identifier, (psr->get(psr))->lexeme);
    else return NULL;
    if(node->identifier == NULL) return NULL;

    /* Parse `as` */
    if(psr->peek(psr)->type == keyword_as) (void)psr->get(psr);
    else return NULL;

    /* Parse expression */
    node->expression = mpir_parse_expression(psr, NEWLINE, 0);
    mpir_display_ast(node->expression, 0);

    append_command(nodes, (union mpir_command_data){.value_assignment = node}, VALUE_ASSIGNMENT);

    return node;
}


struct mpir_on_statement* parse_on_statement(mpir_parser* psr)
{
    /* Parse & discard `on` keyword */
    struct mpir_on_statement* node = calloc(1, sizeof(struct mpir_on_statement));
    if(psr->peek(psr)->type == keyword_on) (void)psr->get(psr);
    else return NULL;

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
    printf("Parsing Trycast!\n");

    /* Parse & Discard `into` keyword */
    if(psr->peek(psr)->type == keyword_into) (void)psr->get(psr);
    else return NULL;
    printf("Parsing Trycast!\n");

    /* Parse 2nd Identifier (casted variable) */
    node->casted_variable = parse_identifier(psr);
    if(node->casted_variable == NULL) return NULL;
    printf("Parsing Trycast!\n");

    /* Parse `\n` */
    if(psr->peek(psr)->type == NEWLINE) (void)psr->get(psr);
    else return NULL;
    printf("Parsing Trycast!\n");

    /* Parse `on` statements */
    node->actions = parse_multiple_on_statements(psr);
    if(node->actions == NULL) return NULL;

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