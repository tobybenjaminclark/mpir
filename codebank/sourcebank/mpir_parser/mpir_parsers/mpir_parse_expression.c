/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../../headerbank/mpir_parser/mpir_parsers/mpir_parse_expression.h"

struct mpir_expression* get_arg(mpir_parser* psr)
{
    if(psr->peek(psr)->type == close_bracket) return NULL;

    struct mpir_expression* arg = calloc(1, sizeof (struct mpir_expression));
    arg = mpir_parse_expression(psr, keyword_comma, 0);
    if(psr->peek(psr)->type == keyword_comma) (void)psr->get(psr);
    return arg;
}

struct mpir_identifier** parse_arguments(mpir_parser* psr)
{
    struct mpir_identifier** nodes = NULL;

    int arg_index = 0;
    struct mpir_expression* arg;
    while((arg = get_arg(psr)) != NULL)
    {
        struct mpir_expression** temp = realloc(nodes, (arg_index + 2) * sizeof(struct mpir_expression*));
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

int mpir_get_op_presedence(mpir_token_type operator)
{
    switch (operator) {
        case operator_sum:
        case operator_subtract:
            return 1;
        case operator_multiply:
        case operator_divide:
            return 2;
        default:
            return 0;
    }
}

void mpir_display_ast(struct mpir_expression* root, int indentation_level)
{
    if (root == NULL)
    {
        printf("Null AST!\n");
        return;
    }

    for (int i = 0; i < indentation_level; i++)
    {
        wprintf(L"-- ");
    }

    /* Display Type */
    switch(root->type)
    {
        case(AST_FUNCTION_CALL):
            wprintf(L"%ls(args)\n", root->data.function_call->identifier->data);
            break;
        case(AST_NUMERICAL_LITERAL):
            wprintf(L"%lf\n", root->data.numerical_literal);
            break;
        case(AST_STRING_LITERAL):
            wprintf(L"%ls\n", root->data.string_literal);
            break;
        case(AST_IDENTIFIER):
            wprintf(L"%ls\n", root->data.identifier);
            break;
        case(AST_OPERATOR):
            wprintf(L"%ls\n", root->data.operator);
            break;
    }

    if (root->left != NULL || root->right != NULL) {
        if (root->left != NULL) {
            mpir_display_ast(root->left, indentation_level + 1);
        }

        if (root->right != NULL) {
            mpir_display_ast(root->right, indentation_level + 1);
        }
    }
}

// Function to create a new number node
struct mpir_expression* mpir_create_numerical_node(long double value)
{
    struct mpir_expression* node = (struct mpir_expression*)malloc(sizeof(struct mpir_expression));
    node->type = AST_NUMERICAL_LITERAL;
    node->data.numerical_literal = value;
    node->left = NULL;
    node->right = NULL;
    return node;
}

// Function to create a new identifier node
struct mpir_expression* mpir_create_identifier_node(struct mpir_identifier* identifier)
{
    struct mpir_expression* node = (struct mpir_expression*)malloc(sizeof(struct mpir_expression));
    node->type = AST_IDENTIFIER;
    wcscpy(node->data.identifier, identifier->data);
    node->left = NULL;
    node->right = NULL;
    return node;
}

// Function to create a new function call node
struct mpir_expression* mpir_create_function_call_node(struct mpir_function_call* call)
{
    struct mpir_expression* node = (struct mpir_expression*)malloc(sizeof(struct mpir_expression));
    node->type = AST_FUNCTION_CALL;
    node->data.function_call = call;
    node->left = NULL;
    node->right = NULL;
    return node;
}

// Function to create a new operator node
struct mpir_expression* mpir_create_operator_node(const wchar_t* operator, struct mpir_expression* left, struct mpir_expression* right) {
    struct mpir_expression* node = (struct mpir_expression*)malloc(sizeof(struct mpir_expression));
    node->type = AST_OPERATOR;
    wcscpy(node->data.operator, operator);
    node->left = left;
    node->right = right;
    return node;
}


struct mpir_expression* mpir_parse_expression(mpir_parser* psr, mpir_token_type delimiter_type, int minimum_precedence)
{
    struct mpir_expression* root = NULL;
    const char* token_names[] = { TOKEN_NAME_MAP };

    while (psr->peek(psr)->type != delimiter_type && psr->peek(psr)->type != NEWLINE &&
           mpir_get_op_presedence(psr->peek(psr)->type) >= minimum_precedence)
    {
        wprintf(L"Expression Lexeme: %ls (type = %s :: %d) \n", psr->peek(psr)->lexeme, token_names[psr->peek(psr)->type], psr->peek(psr)->type);
        if (psr->peek(psr)->type == NUMERICAL_LITERAL)
        {
            printf("EXPR: Parsing Numerical Literal\n");
            root = mpir_create_numerical_node(wcstol(psr->get(psr)->lexeme, NULL, 10));
        }
        else if(psr->peek(psr)->type == IDENTIFIER)
        {
            /* Term is function call */
            if(mpir_parser_peek_k(psr,1)->type == open_bracket)
            {
                /* Parse Function call */
                printf("EXPR: Parsing Function Call\n");
                struct mpir_function_call* func_call = mpir_parse_function_call(psr);
                root = mpir_create_function_call_node(func_call);
            }
            /* Term is identifier */
            else
            {
                printf("EXPR: Parsing Identifier\n");
                /* Parse identifier */
                struct mpir_identifier* identifier = parse_identifier(psr);
                root = mpir_create_identifier_node(identifier);
            }
        }

        else if (psr->peek(psr)->type == open_bracket)
        {
            printf("EXPR: Parsing Open Bracket\n");
            // If an opening parenthesis is encountered, recursively build the AST for the subexpression
            (void)psr->get(psr);
            // Reset minimum_precedence for the subexpression
            struct mpir_expression* subexpression = mpir_parse_expression(psr, NEWLINE, 0);

            root = subexpression;
        }
        else if (psr->peek(psr)->type == close_bracket)
        {
            printf("EXPR: Parsing Closed Bracket\n");
            // If a closing parenthesis is encountered, return the root of the current subexpression
            (void)psr->get(psr);
            return root;
            printf("This shouldn't be reached.");
        }
        else if (psr->peek(psr)->type == operator_sum || psr->peek(psr)->type == operator_subtract)
        {
            printf("EXPR: Parsing Right-Associative Operator\n");
            wchar_t op_lexeme[128];
            wcscpy(op_lexeme, psr->get(psr)->lexeme);

            struct mpir_expression* leftOperand = root;
            struct mpir_expression* rightOperand = mpir_parse_expression(psr, NEWLINE, 0);
            root = mpir_create_operator_node(op_lexeme, leftOperand, rightOperand);
        }
        else if (psr->peek(psr)->type == operator_multiply || psr->peek(psr)->type == operator_divide)
        {
            printf("EXPR: Parsing Left-Associative Operator\n");
            wchar_t op_lexeme[128];
            wcscpy(op_lexeme, psr->get(psr)->lexeme);

            struct mpir_expression* newOperator = mpir_create_operator_node(op_lexeme, NULL, NULL);
            newOperator->left = root;

            struct mpir_expression* rightOperand = mpir_parse_expression(psr, NEWLINE, 0);
            newOperator->right = rightOperand;

            root = newOperator;
        }
        else
        {
            if (root != NULL)
            {
                printf("Unexpected token type: %s\n", token_names[psr->peek(psr)->type]);
                exit(EXIT_FAILURE);  // Or handle the error in a way suitable for your application
            }
            else
            {
                return NULL;
            }
        }
    }
    return root;
}

