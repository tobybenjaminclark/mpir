/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_parser/mpir_parse_expression.h"

struct mpir_expression* mpir_parse_expression(mpir_parser* psr)
{
    return NULL;
}

struct mpir_identifier* get_arg(mpir_parser* psr)
{
    if(psr->peek(psr)->type != IDENTIFIER) return NULL;

    struct mpir_identifier* arg = calloc(1, sizeof (struct mpir_identifier));
    wcscpy(arg->data, psr->get(psr)->lexeme);
    if(psr->peek(psr)->type == keyword_comma) (void)psr->get(psr);
    return arg;
}

struct mpir_identifier** parse_arguments(mpir_parser* psr)
{
    struct mpir_identifier** nodes = NULL;

    int arg_index = 0;
    struct mpir_identifier* arg;
    while((arg = get_arg(psr)) != NULL)
    {
        struct mpir_identifier** temp = realloc(nodes, (arg_index + 2) * sizeof(struct mpir_identifier*));
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

struct mpir_function_call* mpir_parse_function_call(mpir_parser* psr)
{
    /*  identifier `(` arg0 `,` arg1 `,` ... argn `)` */

    struct mpir_function_call* node = malloc(sizeof(struct mpir_function_call));

    /* Parse function identifier */
    if(psr->peek(psr)->type == IDENTIFIER) node->identifier = parse_function_identifier(psr);
    else return NULL;

    /* Parse `(` */
    if(psr->peek(psr)->type == open_bracket) (void)psr->get(psr);
    else return NULL;

    /* Parse Arguments */
    node->arguments = parse_arguments(psr);
    if(node->arguments == NULL) return NULL;

    /* Parse `)` */
    if(psr->peek(psr)->type == close_bracket) (void)psr->get(psr);
    else return NULL;

    return node;
}

int isOperator(char ch) {
    return (ch == '+' || ch == '-' || ch == '*' || ch == '/');
}

int getPrecedence(mpir_token_type operator)
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

void displayASTIndented(Node* root, int indentLevel)
{
    if (root == NULL) {
        printf("Null AST!\n");
        return;
    }

    for (int i = 0; i < indentLevel; i++) {
        wprintf(L"-- ");
    }

    if (root->type == 'n') {
        wprintf(L"%lf\n", root->value);
    } else if (root->type == 'o') {
        wprintf(L"%ls\n", root->operator);
    }

    if (root->left != NULL || root->right != NULL) {
        if (root->left != NULL) {
            displayASTIndented(root->left, indentLevel + 1);
        }

        if (root->right != NULL) {
            displayASTIndented(root->right, indentLevel + 1);
        }
    }
}

// Function to create a new number node
Node* createNumberNode(double value)
{
    Node* node = (Node*)malloc(sizeof(Node));
    node->type = 'n';
    node->value = value;
    node->left = NULL;
    node->right = NULL;
    return node;
}

// Function to create a new operator node
Node* createOperatorNode(const wchar_t* operator, Node* left, Node* right) {
    Node* node = (Node*)malloc(sizeof(Node));
    node->type = 'o';
    wcscpy(node->operator, operator);
    node->left = left;
    node->right = right;
    return node;
}


Node* buildAST(mpir_parser* psr, mpir_token_type delimiter_type, int minPrecedence)
{
    Node* root = NULL;
    const char* token_names[] = { TOKEN_NAME_MAP };

    while (psr->peek(psr)->type != delimiter_type && psr->peek(psr)->type != NEWLINE && getPrecedence(psr->peek(psr)->type) >= minPrecedence)
    {
        wprintf(L"Expression Lexeme: %ls (type = %s :: %d) \n", psr->peek(psr)->lexeme, token_names[psr->peek(psr)->type], psr->peek(psr)->type);
        if (psr->peek(psr)->type == NUMERICAL_LITERAL)
        {
            printf("EXPR: Parsing Numerical Literal\n");
            root = createNumberNode(wcstol(psr->get(psr)->lexeme, NULL, 10));
        }
        else if (psr->peek(psr)->type == open_bracket)
        {
            printf("EXPR: Parsing Open Bracket\n");
            // If an opening parenthesis is encountered, recursively build the AST for the subexpression
            (void)psr->get(psr);
            Node* subexpression = buildAST(psr, NEWLINE, 0);  // Reset minPrecedence for the subexpression
            root = subexpression;
        }
        else if (psr->peek(psr)->type == close_bracket)
        {
            printf("EXPR: Parsing Closed Bracket\n");
            // If a closing parenthesis is encountered, return the root of the current subexpression
            (void)psr->get(psr);
            return root;
        }
        else if (psr->peek(psr)->type == operator_sum || psr->peek(psr)->type == operator_subtract)
        {
            printf("EXPR: Parsing Right-Associative Operator\n");
            wchar_t op_lexeme[128];
            wcscpy(op_lexeme, psr->get(psr)->lexeme);

            Node* leftOperand = root;
            Node* rightOperand = buildAST(psr, NEWLINE, getPrecedence(psr->peek(psr)->type));
            root = createOperatorNode(op_lexeme, leftOperand, rightOperand);
        }
        else if (psr->peek(psr)->type == operator_multiply || psr->peek(psr)->type == operator_divide)
        {
            printf("EXPR: Parsing Left-Associative Operator\n");
            wchar_t op_lexeme[128];
            wcscpy(op_lexeme, psr->get(psr)->lexeme);

            Node* leftOperand = root;
            Node* rightOperand = buildAST(psr, NEWLINE, getPrecedence(psr->peek(psr)->type) + 1);  // Adjust minPrecedence for left-associative operators
            root = createOperatorNode(op_lexeme, leftOperand, rightOperand);
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

