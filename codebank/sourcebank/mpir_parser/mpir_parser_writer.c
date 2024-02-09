/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_parser/mpir_parser_writer.h"

#include <stdio.h>

/*
   struct mpir_ast_expression
    {
        int type;
    union {
        struct mpir_ast_function_call* function_call;
        long double numerical_literal;
        wchar_t identifier[128];
        wchar_t string_literal[128];
        wchar_t operator[128];
    } data;
    struct mpir_ast_expression* left;
    struct mpir_ast_expression* right;
    };
 */
struct wjson* mpir_wjsonify_expression(struct mpir_ast_expression* expr)
{
    struct wjson* wjson_node = wjson_initialize();
    switch(expr->type)
    {
        case AST_IDENTIFIER:
            printf("");
            wjson_append_string(wjson_node, L"TYPE", L"EXPRESSION_IDENTIFIER");
            wjson_append_string(wjson_node, L"IDENTIFIER", expr->data.identifier);
            break;

        case AST_STRING_LITERAL:
            printf("");
            wjson_append_string(wjson_node, L"TYPE", L"EXPRESSION_STRING_LITERAL");
            wjson_append_string(wjson_node, L"IDENTIFIER", expr->data.string_literal);
            break;

        case AST_OPERATOR:
            printf("");
            wjson_append_string(wjson_node, L"TYPE", L"EXPRESSION_OPERATOR");
            wjson_append_string(wjson_node, L"IDENTIFIER", expr->data.operator);
            break;

        case AST_NUMERICAL_LITERAL:
            printf("");
            wjson_append_string(wjson_node, L"TYPE", L"EXPRESSION_NUMERICAL_LITERAL");
            wjson_append_numerical(wjson_node, L"VALUE", expr->data.numerical_literal);
            break;
    }

    if(expr->left != NULL) wjson_append_object(wjson_node, L"LEFT", mpir_wjsonify_expression(expr->left));
    if(expr->right != NULL) wjson_append_object(wjson_node, L"RIGHT", mpir_wjsonify_expression(expr->right));
    return wjson_node;

}

void mpir_wjsonify_command(struct mpir_command_node* node, struct wjson* wjson_list)
{
    switch (node->type)
    {
        case VALUE_ASSIGNMENT:
            printf("");
            struct wjson* wjson_node = wjson_initialize();
            wjson_append_string(wjson_node, L"TYPE", L"VALUE_ASSIGNMENT");
            wjson_append_string(wjson_node, L"IDENTIFIER", node->data.value_assignment->identifier);
            wjson_append_object(wjson_node, "EXPRESSION", mpir_wjsonify_expression(node->data.value_assignment->expression));
            wjson_list_append_object(wjson_list, wjson_node);
            return;

        case TYPE_ASSIGNMENT:
            printf("");
            struct wjson* wjson_node2 = wjson_initialize();
            wjson_append_string(wjson_node2, L"TYPE", L"TYPE_ASSIGNMENT");
            wjson_append_string(wjson_node2, L"IDENTIFIER", node->data.type_assignment->identifier);
            wjson_append_string(wjson_node2, L"TYPE", node->data.type_assignment->type);
            wjson_list_append_object(wjson_list, wjson_node2);
            return;

        case FUNCTION_CALL:
            printf("");
            struct wjson* wjson_node3 = wjson_initialize();
            wjson_append_string(wjson_node3, L"TYPE", L"FUNCTION_CALL");
            wjson_append_string(wjson_node3, L"IDENTIFIER", node->data.function_call->identifier);

            /* Arguments */
            int argument_count = 0;

            struct wjson* current_argument;
            struct wjson* arguments = wjson_initialize_list();
            while (node->data.function_call->arguments[argument_count] != NULL)
            {
                current_argument = wjson_initialize();
                wjson_append_string(current_argument, L"TYPE", L"FUNCTION_ARGUMENT");
                wjson_append_numerical(current_argument, L"ARGUMENT_INDEX", (double)argument_count);
                wjson_append_object(current_argument, L"VALUE", mpir_wjsonify_expression(node->data.function_call->arguments[argument_count]));

                wjson_list_append_object(arguments, current_argument);
                argument_count++;
            }


            wjson_append_list(wjson_node3, L"ARGUMENTS", arguments);
            wjson_list_append_object(wjson_list, wjson_node3);
            return;

        case TRYCAST_STATEMENT:
            printf("");
            struct wjson* wjson_node4 = wjson_initialize();
            wjson_append_string(wjson_node4, L"TYPE", L"TRYCAST_STATEMENT");
            wjson_append_string(wjson_node4, L"DOMINANT_IDENTIFIER", node->data.trycast_statement->dominant_variable);
            wjson_append_string(wjson_node4, L"CASTED_IDENTIFIER", node->data.trycast_statement->casted_variable);


            wjson_list_append_object(wjson_list, wjson_node4);
            return;

        case DO_STATEMENT:
            printf("");
            struct wjson* wjson_node5 = wjson_initialize();
            wjson_append_string(wjson_node5, L"TYPE", L"DO_STATEMENT");
            wjson_list_append_object(wjson_list, wjson_node5);
            return;
    }
    return;
}

void mpir_wjsonify_command_list(struct mpir_command_list* body, struct wjson* wjson_list)
{
    struct mpir_command_node* command_node = body->head;
    while(command_node != NULL)
    {
        mpir_wjsonify_command(command_node, wjson_list);
        command_node = command_node->next;
    }
}

void mpir_wjsonify_docsection(struct mpir_ast_docsection* docsection, struct wjson* wjson_list)
{
    /* Setup JSON List Structure */
    struct wjson* wjson_docinstance;

    /* Append each doc instance */
    struct mpir_command_node* doc_node = docsection->docs->head;
    while (doc_node != NULL)
    {
        wjson_docinstance = wjson_initialize();
        wjson_append_string(wjson_docinstance, L"FLAG", doc_node->data.doc_statement->flag_type->data);
        if(doc_node->data.doc_statement->variable->data != NULL)
            wjson_append_string(wjson_docinstance, L"IDENTIFIER", doc_node->data.doc_statement->variable->data);
        wjson_append_string(wjson_docinstance, L"STRING", doc_node->data.doc_statement->documentation);

        wjson_list_append_object(wjson_list, wjson_docinstance);
        doc_node = doc_node->next;
    }
}

int mpir_write_ast(mpir_parser* psr, char path[])
{
    FILE *file = fopen(path, "w");

    if (file == NULL)
    {
        fprintf(stderr, "Error opening file %s for writing.\n", path);
        return 0; // Return 0 to indicate failure
    }

    fprintf(file, "\nWriting JSON to file.\n");
    printf("\n");

    /* Create wJson node for program */
    struct wjson* wjson_commands = wjson_initialize_list();

    struct mpir_command_node* program_node = psr->program->head;
    while (program_node != NULL)
    {
        switch (program_node->type)
        {
            case FUNCTION_DECLARATION:
                fprintf(file, "FUNCTION_DECLARATION\n");

                /* Generate JSON for Type, Identifier & Return Type */
                struct wjson* wjson_funcdef = wjson_initialize();
                wjson_append_string(wjson_funcdef, L"TYPE", L"FUNCTION_DECLARATION");
                wjson_append_string(wjson_funcdef, L"IDENTIFIER", program_node->data.function_declaration->identifier->data);
                wjson_append_string(wjson_funcdef, L"RETURN_TYPE", program_node->data.function_declaration->return_type->data);

                /* Generate JSON for Input Types */
                struct wjson* wjson_funcdef_inputs = wjson_initialize_list();
                int argument_count1 = 0;
                while (program_node->data.function_declaration->inputs[argument_count1] != NULL)
                {
                    wjson_list_append_string(wjson_funcdef_inputs, program_node->data.function_declaration->inputs[argument_count1]->data);
                    argument_count1++;
                }

                struct wjson* wjson_funcdef_body = wjson_initialize_list();
                /* Generate JSON for body */

                /* Generate JSON for docsection */
                struct wjson* wjson_funcdef_docsection = wjson_initialize_list();
                mpir_wjsonify_docsection(program_node->data.function_declaration->docsection, wjson_funcdef_docsection);

                /* Generate JSON for program */
                struct wjson* wjson_funcdef_statements = wjson_initialize_list();
                mpir_wjsonify_command_list(program_node->data.function_declaration->body, wjson_funcdef_statements);

                /* Append to WJSON_Commands */
                wjson_append_list(wjson_funcdef, L"BODY", wjson_funcdef_statements);
                wjson_append_list(wjson_funcdef, L"DOCSECTION", wjson_funcdef_docsection);
                wjson_append_list(wjson_funcdef, L"INPUTS", wjson_funcdef_inputs);
                wjson_list_append_object(wjson_commands, wjson_funcdef);
                break;

            case NEW_TYPE_DECLARATION:
                fprintf(file, "TYPE_DECLARATION\n");
                break;
            default:
                break;
        }
        program_node = program_node->next;
    }

    fclose(file); // Close the file

    struct wjson* wjson_master = wjson_initialize();
    wjson_append_list(wjson_master, L"contents", wjson_commands);
    wjson_print(wjson_master, 0);

    return 1; // Return 1 to indicate success
}