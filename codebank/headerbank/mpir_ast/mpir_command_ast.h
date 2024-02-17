/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_COMMAND_AST_H
#define MPIR_COMPILER_MPIR_COMMAND_AST_H

#include "../../headerbank/mpir_token/mpir_token.h"
#include "../../headerbank/mpir_ast/mpir_expression_ast.h"
#include "../../headerbank/mpir_ast/mpir_doc_ast.h"
#include "../mpir_misc/mpir_linked_list.h"



/**
 * @struct mpir_ast_type_assignment
 * @brief Represents a type assignment in the Abstract Syntax Tree (AST).
 *
 * This structure captures information about assigning a type to a variable. (let statement)
 */
struct mpir_ast_type_assignment
{
    wchar_t* identifier[128];                       /** ← Identifier associated with the type assignment.                   */
    wchar_t* type[128];                             /** ← Type associated with the type assignment.                         */
};



/**
 * @struct mpir_ast_value_assignment
 * @brief Represents a value assignment in the Abstract Syntax Tree (AST).
 *
 * This structure represents the assignment of a value to a variable in the AST. (set statement)
 */
struct mpir_ast_value_assignment
{
    wchar_t* identifier[128];                       /** ← Identifier associated with the value assignment.                  */
    struct mpir_ast_expression* expression;         /** ← Expression assigned to the variable.                              */
};



/**
 * @struct mpir_ast_on_statement
 * @brief Represents an 'on' statement in the Abstract Syntax Tree (AST).
 *
 * This structure is part of the AST and is used to define actions based on certain conditions.
 */
struct mpir_ast_on_statement
{
    union{
        double mpir_numerical_literal;              /** ← Numerical literal value.                                          */
        wchar_t* mpir_string_literal;               /** ← String literal value.                                             */
    } literal;                                      /** ← Union of possible literal data.                                   */
    enum stored_type {
        numerical_literal,                          /** ← Indicates the stored type is numerical.                           */
        string_literal                              /** ← Indicates the stored type is a string.                            */
    } stored_type;                                  /** ← Enum indicating the stored type.                                  */
    struct mpir_command_list* commands;             /** ← Pointer to a list of commands associated with the 'on' statement. */
};



/**
 * @struct mpir_ast_trycast_statement
 * @brief Represents a 'trycast' statement in the Abstract Syntax Tree (AST).
 *
 * This structure represents the 'trycast' statement, attempting to cast a variable into another type.
 */
struct mpir_ast_trycast_statement
{
    struct mpir_ast_identifier* dominant_variable;  /** ← Dominant variable in the trycast statement.                     */
    struct mpir_ast_identifier* casted_variable;    /** ← Casted variable in the trycast statement.                       */
    struct mpir_ast_on_statement** actions;         /** ← Array of 'on' statements associated with the trycast statement. */
};



/**
 * @struct mpir_ast_do_statement
 * @brief Represents a 'do' statement in the Abstract Syntax Tree (AST).
 *
 * This structure represents the 'do' statement, involving a expression call and associated actions.
 */
struct mpir_ast_do_statement
{
    struct mpir_ast_expression* expression;         /** ← Function call in the 'do' statement.                         */
    struct mpir_ast_on_statement** actions;          /** ← Array of 'on' statements associated with the 'do' statement. */
};

#endif
