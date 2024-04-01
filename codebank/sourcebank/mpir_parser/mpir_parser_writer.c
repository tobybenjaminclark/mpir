/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_parser/mpir_parser_writer.h"

#include <stdio.h>

/*
enum type_logic_operator
{
GT,         /** ← Greater than              /
GTEQ,       /** ← Greater than or equal to  *
LT,         /** ← Less than                 *
LTEQ,       /** ← Less than or equal to     *
EQ,         /** ← Equal to                  *
AND,        /** ← Logical AND               *
OR,         /** ← Logical OR                *
NOT,        /** ← Logical NOT               *
FORALL,     /** ← Universal quantifier      *
EXISTS,     /** ← Existential quantifier    *
INVALID     /** ← Invalid operator          *
};

/**
 * @enum type_logic_type
 * @brief Enumeration of types in type logic expressions.
 *
enum type_logic_type
{
    type_OPERATOR,      /** ← Operator type          *
    type_IDENTIFIER,    /** ← Identifier type        *
    type_NUMERICAL,     /** ← Numerical literal type *
    type_STRING         /** ← String literal type    *
};
 *
 * struct type_logic
{
    enum type_logic_type type; /**< Type of the logic node.
union {
    enum type_logic_operator op;        * ← Logic operator data.                                   *
    struct mpir_ast_identifier* id;     ** ← Identifier data.                                       *
    wchar_t* str_literal;               ** ← String literal data.                                   *
    double num_literal;                 ** ← Numerical literal data.                                *
} data;                                 ** ← Union of possible data associated with the logic node. *
struct type_logic* left;                ** ← Pointer to the left subexpression.                     *
struct type_logic* right;               ** ← Pointer to the right subexpression.                    *
};

*/
const wchar_t* get_str_from_logic_operator(enum type_logic_operator op)
{
    switch (op) {
        case GT:
            return L">";
        case GTEQ:
            return L"≥";
        case LT:
            return L"<";
        case LTEQ:
            return L"≤";
        case EQ:
            return L"=";
        case AND:
            return L"∧";
        case OR:
            return L"∨";
        case NOT:
            return L"¬";
        case FORALL:
            return L"∀";
        case EXISTS:
            return L"∃";
        default:
            return L"Invalid operator";
    }
}

struct wjson* mpir_wjsonify_type_logic(struct type_logic* logic)
{
    struct wjson* wjson_node = wjson_initialize();

    switch(logic->type)
    {
        case type_OPERATOR:
            wjson_append_string(wjson_node, L"DATATYPE", L"OPERATOR");
            wjson_append_string(wjson_node, L"DATA", get_str_from_logic_operator(logic->data.op));
            break;
        case type_IDENTIFIER:
            wjson_append_string(wjson_node, L"DATATYPE", L"IDENTIFIER");
            wjson_append_string(wjson_node, L"DATA", logic->data.id->data);
            break;
        case type_STRING:
            wjson_append_string(wjson_node, L"DATATYPE", L"STRING_LITERAL");
            wjson_append_string(wjson_node, L"DATA", logic->data.str_literal);
            break;
        case type_NUMERICAL:
            wjson_append_string(wjson_node, L"DATATYPE", L"NUMERICAL_LITERAL");
            wjson_append_numerical(wjson_node, L"DATA", logic->data.num_literal);
            break;
    }

    if(logic->left != NULL) wjson_append_object(wjson_node, L"LEFT", mpir_wjsonify_type_logic(logic->left));
    if(logic->right != NULL) wjson_append_object(wjson_node, L"RIGHT", mpir_wjsonify_type_logic(logic->right));
    return wjson_node;
}

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
        case AST_FUNCTION_CALL:
            wjson_append_string(wjson_node, L"TYPE", L"FUNCTION_CALL");
            wjson_append_string(wjson_node, L"IDENTIFIER", expr->data.function_call->identifier);

            /* Arguments */
            int argument_count = 0;

            struct wjson* current_argument;
            struct wjson* arguments = wjson_initialize_list();
            while (expr->data.function_call->arguments[argument_count] != NULL)
            {
                current_argument = wjson_initialize();
                wjson_append_string(current_argument, L"TYPE", L"FUNCTION_ARGUMENT");
                wjson_append_numerical(current_argument, L"ARGUMENT_INDEX", (double)argument_count);
                wjson_append_object(current_argument, L"VALUE", mpir_wjsonify_expression(expr->data.function_call->arguments[argument_count]));

                wjson_list_append_object(arguments, current_argument);
                argument_count++;
            }
            wjson_append_list(wjson_node, L"ARGUMENTS", arguments);
            break;

        case AST_LIST:
            wjson_append_string(wjson_node, L"TYPE", L"LIST");

            /* Arguments */
            int argument_countx = 0;

            struct wjson* current_argumentx;
            struct wjson* argumentsx = wjson_initialize_list();
            while (expr->data.function_call->arguments[argument_countx] != NULL)
            {
                current_argumentx = wjson_initialize();
                wjson_append_string(current_argumentx, L"TYPE", L"LIST_NODE");
                wjson_append_numerical(current_argumentx, L"INDEX", (double)argument_count);
                wjson_append_object(current_argumentx, L"VALUE", mpir_wjsonify_expression(expr->data.function_call->arguments[argument_countx]));

                wjson_list_append_object(argumentsx, current_argumentx);
                argument_countx++;
            }
            wjson_append_list(wjson_node, L"NODES", argumentsx);
            break;

        case AST_IDENTIFIER:
            wjson_append_string(wjson_node, L"TYPE", L"EXPRESSION_IDENTIFIER");
            wjson_append_string(wjson_node, L"IDENTIFIER", expr->data.identifier);
            break;

        case AST_STRING_LITERAL:
            wjson_append_string(wjson_node, L"TYPE", L"EXPRESSION_STRING_LITERAL");
            wjson_append_string(wjson_node, L"IDENTIFIER", expr->data.string_literal);
            break;

        case AST_OPERATOR:
            wjson_append_string(wjson_node, L"TYPE", L"EXPRESSION_OPERATOR");
            wjson_append_string(wjson_node, L"IDENTIFIER", expr->data.operator);
            break;

        case AST_NUMERICAL_LITERAL:
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
            wjson_append_object(wjson_node, L"EXPRESSION", mpir_wjsonify_expression(node->data.value_assignment->expression));
            wjson_list_append_object(wjson_list, wjson_node);
            return;




        case TYPE_ASSIGNMENT:
            printf("");
            struct wjson* wjson_node2 = wjson_initialize();
            wjson_append_string(wjson_node2, L"TYPE", L"TYPE_ASSIGNMENT");
            wjson_append_string(wjson_node2, L"IDENTIFIER", node->data.type_assignment->identifier);
            wjson_append_string(wjson_node2, L"ASSIGNED_TYPE", node->data.type_assignment->type);
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

            int argument_count3 = 0;
            struct wjson* on_statement;
            struct wjson* on_statements = wjson_initialize_list();
            while (node->data.trycast_statement->actions[argument_count3] != NULL)
            {
                on_statement = wjson_initialize();
                wjson_append_string(on_statement, L"TYPE", L"ON_STATEMENT");
                if(node->data.trycast_statement->actions[argument_count3]->stored_type == string_literal)
                {
                    wjson_append_string(on_statement, L"MATCH_TYPE", L"STRING_LITERAL");
                    wjson_append_string(on_statement, L"MATCH_VALUE",
                                        node->data.trycast_statement->actions[argument_count3]->literal.mpir_string_literal);
                }
                else if(node->data.trycast_statement->actions[argument_count3]->stored_type == numerical_literal)
                {
                    wjson_append_string(on_statement, L"MATCH_TYPE", L"NUMERICAL_LITERAL");
                    wjson_append_numerical(on_statement, L"MATCH_VALUE", node->data.trycast_statement->actions[argument_count3]->literal.mpir_numerical_literal);

                }

                struct wjson* wjson_do_commands  = wjson_initialize_list();
                mpir_wjsonify_command_list(node->data.trycast_statement->actions[argument_count3]->commands, wjson_do_commands);

                wjson_append_list(on_statement, L"MATCH_COMMANDS", wjson_do_commands);

                wjson_list_append_object(on_statements, on_statement);
                argument_count3++;
            }

            wjson_append_list(wjson_node4, L"ON_STATEMENTS", on_statements);
            wjson_list_append_object(wjson_list, wjson_node4);
            return;




        case DO_STATEMENT:
            printf("");
            struct wjson* wjson_node5 = wjson_initialize();

            wjson_append_string(wjson_node5, L"TYPE", L"DO_STATEMENT");
            wjson_append_object(wjson_node5, L"EXPRESSION", mpir_wjsonify_expression(node->data.do_statement->expression));

            int argument_count4 = 0;
            struct wjson* on_statement2;
            struct wjson* on_statements2 = wjson_initialize_list();
            while (node->data.do_statement->actions[argument_count4] != NULL)
            {
                on_statement2 = wjson_initialize();
                wjson_append_string(on_statement2, L"TYPE", L"ON_STATEMENT");
                if(node->data.do_statement->actions[argument_count4]->stored_type == string_literal)
                {
                    wjson_append_string(on_statement2, L"MATCH_TYPE", L"STRING_LITERAL");
                    wjson_append_string(on_statement2, L"MATCH_VALUE",
                                        node->data.do_statement->actions[argument_count4]->literal.mpir_string_literal);
                }
                else if(node->data.do_statement->actions[argument_count4]->stored_type == numerical_literal)
                {
                    wjson_append_string(on_statement2, L"MATCH_TYPE", L"NUMERICAL_LITERAL");
                    wjson_append_numerical(on_statement2, L"MATCH_VALUE", node->data.do_statement->actions[argument_count4]->literal.mpir_numerical_literal);

                }

                struct wjson* wjson_do_commands  = wjson_initialize_list();
                mpir_wjsonify_command_list(node->data.do_statement->actions[argument_count4]->commands, wjson_do_commands);

                wjson_append_list(on_statement2, L"MATCH_COMMANDS", wjson_do_commands);

                wjson_list_append_object(on_statements2, on_statement2);
                argument_count4++;
            }

            wjson_append_list(wjson_node5, L"ON_STATEMENTS", on_statements2);
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

    /* Create wJson node for program */
    struct wjson* wjson_commands = wjson_initialize_list();

    struct mpir_command_node* program_node = psr->program->head;
    while (program_node != NULL)
    {
        switch (program_node->type)
        {
            case FUNCTION_DECLARATION:
                {};
                /* Generate JSON for Type, Identifier & Return Type */
                struct wjson* wjson_funcdef = wjson_initialize();
                wjson_append_string(wjson_funcdef, L"TYPE", L"FUNCTION_DECLARATION");
                wjson_append_string(wjson_funcdef, L"IDENTIFIER", program_node->data.function_declaration->identifier->data);
                wjson_append_string(wjson_funcdef, L"RETURN_TYPE", program_node->data.function_declaration->return_type->data);
                wjson_append_numerical(wjson_funcdef, L"RETURN_TYPE_LIST", program_node->data.function_declaration->return_type->list);

                /* Generate JSON for Input Types */
                struct wjson* wjson_funcdef_inputs = wjson_initialize_list();
                int argument_count1 = 0;
                while (program_node->data.function_declaration->input_types[argument_count1] != NULL)
                {
                    struct wjson* wjson_funcdef_input_i = wjson_initialize();
                    wjson_append_string(wjson_funcdef_input_i, L"TYPE", program_node->data.function_declaration->input_types[argument_count1]->data);
                    wjson_append_numerical(wjson_funcdef_input_i, L"LIST_INDENTATION", program_node->data.function_declaration->input_types[argument_count1]->list);
                    wjson_list_append_object(wjson_funcdef_inputs, wjson_funcdef_input_i);
                    argument_count1++;
                }

                /* Generate JSON for Input Types */
                struct wjson* wjson_funcdef_arguments = wjson_initialize_list();
                int argument_count2 = 0;
                while (program_node->data.function_declaration->arguments[argument_count2] != NULL)
                {
                    wjson_list_append_string(wjson_funcdef_arguments, program_node->data.function_declaration->arguments[argument_count2]->data);
                    argument_count2++;
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
                wjson_append_list(wjson_funcdef, L"ARGUMENTS", wjson_funcdef_arguments);
                wjson_list_append_object(wjson_commands, wjson_funcdef);
                break;

            case NEW_TYPE_DECLARATION:
                {};
                /* Generate JSON for Type, Identifier & Return Type */
                struct wjson* wjson_typedef = wjson_initialize();
                struct wjson* wjson_typedef_docsection = wjson_initialize_list();
                wjson_append_string(wjson_typedef, L"TYPE", L"TYPE_DECLARATION");
                wjson_append_string(wjson_typedef, L"IDENTIFIER", program_node->data.type_declaration->identifier->data);
                mpir_wjsonify_docsection(program_node->data.type_declaration->docsection, wjson_typedef_docsection);

                struct wjson* wjson_typedef_inputs = wjson_initialize_list();
                int type_dec_count1 = 0;
                while (program_node->data.type_declaration->inputs[type_dec_count1] != NULL)
                {
                    wjson_list_append_string(wjson_typedef_inputs, program_node->data.type_declaration->inputs[type_dec_count1]->data);
                    type_dec_count1++;
                }

                wjson_append_list(wjson_typedef, L"DOCSECTION", wjson_typedef_docsection);
                wjson_append_list(wjson_typedef, L"INPUTS", wjson_typedef_inputs);
                wjson_append_string(wjson_typedef, L"BASE_TYPE", program_node->data.type_declaration->base_type->data);
                wjson_append_numerical(wjson_typedef, L"BASE_TYPE_LIST", program_node->data.type_declaration->base_type->list);
                wjson_append_object(wjson_typedef, L"LOGIC", mpir_wjsonify_type_logic(program_node->data.type_declaration->refinement));
                wjson_list_append_object(wjson_commands, wjson_typedef);
                break;
            default:
                break;
        }
        program_node = program_node->next;
    }


    struct wjson* wjson_master = wjson_initialize();
    wjson_append_list(wjson_master, L"CONTENTS", wjson_commands);

    FILE* outputFile = fopen(path, "w");
    if (outputFile == NULL)
    {
        wprintf(L"Error opening the file for writing.\n");
        return 1;
    }

    wjson_fprint(outputFile, wjson_master, 0);

    fclose(outputFile);

    return 1; // Return 1 to indicate success
}