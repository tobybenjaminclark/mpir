/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_parser/mpir_parse.h"

void print_command_node(struct mpir_command_node* current_node)
{
    switch(current_node->type)
    {
        case VALUE_ASSIGNMENT:
            wprintf(L"\t\tValue Assignment `%ls` to expression:\n", current_node->data.value_assignment->identifier);
            mpir_display_ast(current_node->data.value_assignment->expression, 2);
            break;
        case TYPE_ASSIGNMENT:
            wprintf(L"\t\tType Assignment `%ls` to type `%ls`\n", current_node->data.type_assignment->identifier, current_node->data.type_assignment->type);
            break;
        case FUNCTION_CALL:
            wprintf(L"\t\tFunction call to '%ls':\n", current_node->data.function_call->identifier->data);
            int argument_count = 0;
            while (current_node->data.function_call->arguments[argument_count] != NULL) {
                wprintf(L"\t\t\t| Argument %d:\n", argument_count);
                mpir_display_ast(current_node->data.function_call->arguments[argument_count], 3);
                argument_count++;
            }
            break;

        case FUNCTION_DECLARATION:
            wprintf(L"Function Declaration :: %ls \n\tInput Types:\n", current_node->data.function_declaration->identifier->data);
            int argument_count2 = 0;
            while (current_node->data.function_declaration->inputs[argument_count2] != NULL) {
                wprintf(L"\t\tInput %d: %ls\n", argument_count2, current_node->data.function_declaration->inputs[argument_count2]->data);
                argument_count2++;
            }
            wprintf(L"\tReturn Type: %ls\n\tBody:\n", current_node->data.function_declaration->return_type->data);

            struct mpir_command_node* command_node = current_node->data.function_declaration->body->head;
            while(command_node != NULL)
            {
                print_command_node(command_node);
                command_node = command_node->next;
            }
            break;
        case TRYCAST_STATEMENT:
            wprintf(L"\t\tTrycast of `%ls` into `%ls`\n", current_node->data.trycast_statement->dominant_variable->data, current_node->data.trycast_statement->casted_variable->data);
            int argument_count3 = 0;
            while (current_node->data.trycast_statement->actions[argument_count3] != NULL)
            {
                if(current_node->data.trycast_statement->actions[argument_count3]->stored_type == string_literal) wprintf(L"\t\t\t%d. on `%ls` do:", argument_count3, current_node->data.trycast_statement->actions[argument_count3]->literal.mpir_string_literal);
                else if(current_node->data.trycast_statement->actions[argument_count3]->stored_type == numerical_literal) wprintf(L"\t\t\t%d. on `%f` do:", argument_count3, current_node->data.trycast_statement->actions[argument_count3]->literal.mpir_string_literal);
                print_command_node(current_node->data.trycast_statement->actions[argument_count3]->commands->head);
                argument_count3++;
            }
            break;
        case DO_STATEMENT:
            wprintf(L"\t\tDo Statment: ");
            wprintf(L"Function call to '%ls':\n", current_node->data.do_statement->function->identifier->data);
            int argument_count4 = 0;
            while (current_node->data.do_statement->function->arguments[argument_count4] != NULL) {
                wprintf(L"\t\t\t| Argument %d:\n", argument_count);
                mpir_display_ast(current_node->data.do_statement->function->arguments[argument_count4], 3);
                argument_count4++;
            }

            int argument_count5 = 0;
            while (current_node->data.do_statement->actions[argument_count5] != NULL)
            {
                if(current_node->data.do_statement->actions[argument_count5]->stored_type == string_literal) wprintf(L"\t\t\t%d. on `%ls` do:", argument_count5, current_node->data.do_statement->actions[argument_count5]->literal.mpir_string_literal);
                else if(current_node->data.do_statement->actions[argument_count5]->stored_type == numerical_literal) wprintf(L"\t\t\t%d. on `%f` do:", argument_count5, current_node->data.do_statement->actions[argument_count5]->literal.mpir_string_literal);
                print_command_node(current_node->data.do_statement->actions[argument_count5]->commands->head);
                argument_count5++;
            }
            break;
        default:
            break;
    }
}

void mpir_parse(mpir_parser* parser)
{
    mpir_token_type next_type;
    mpir_token* current_token = parser->get(parser);
    while(current_token != NULL)
    {
        if(parser->peek(parser) != NULL)
        {
            next_type = (parser->peek(parser))->type;
            if(next_type == keyword_funcdef)
            {
                parse_function_declaration(parser);
            }
        }
        else next_type = (mpir_token_type) NULL;

        current_token = parser->get(parser);
    }

    struct mpir_command_node* program_node = parser->program->head;
    while(program_node != NULL)
    {
        print_command_node(program_node);
        program_node = program_node->next;
    }


    return;
}