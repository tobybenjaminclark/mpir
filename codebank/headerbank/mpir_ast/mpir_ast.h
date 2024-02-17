/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_AST_H
#define MPIR_COMPILER_MPIR_AST_H

#include "../../headerbank/mpir_token/mpir_token.h"
#include "../../headerbank/mpir_ast/mpir_command_ast.h"
#include "../../headerbank/mpir_ast/mpir_doc_ast.h"
#include "../../headerbank/mpir_misc/mpir_linked_list.h"

/**
 * @struct mpir_ast_function_declaration
 * @brief Represents a expression declaration in the Abstract Syntax Tree (AST).
 *
 * This structure captures information about a expression declaration, including its identifier, input types,
 * return type, body, and associated documentation section.
 */
struct mpir_ast_function_declaration
{
    struct mpir_ast_identifier* identifier;    /** ← Identifier of the expression.                                        */
    struct mpir_ast_identifier** arguments;    /** ← Identifiers of Arguments (Types sequential to input_types          */
    struct mpir_ast_type** input_types;        /** ← Array of input types for the expression.                             */
    struct mpir_ast_type* return_type;         /** ← Return type of the expression.                                       */
    struct mpir_command_list* body;            /** ← Pointer to the body of the expression.                               */
    struct mpir_ast_docsection* docsection;    /** ← Pointer to the documentation section associated with the expression. */
};

/**
 * @enum type_logic_operator
 * @brief Enumeration of logic operators used in type logic expressions.
 */
enum type_logic_operator
{
    GT,         /** ← Greater than              */
    GTEQ,       /** ← Greater than or equal to  */
    LT,         /** ← Less than                 */
    LTEQ,       /** ← Less than or equal to     */
    EQ,         /** ← Equal to                  */
    AND,        /** ← Logical AND               */
    OR,         /** ← Logical OR                */
    NOT,        /** ← Logical NOT               */
    FORALL,     /** ← Universal quantifier      */
    EXISTS,     /** ← Existential quantifier    */
    INVALID     /** ← Invalid operator          */
};

/**
 * @enum type_logic_type
 * @brief Enumeration of types in type logic expressions.
 */
enum type_logic_type
{
    type_OPERATOR,      /** ← Operator type          */
    type_IDENTIFIER,    /** ← Identifier type        */
    type_NUMERICAL,     /** ← Numerical literal type */
    type_STRING         /** ← String literal type    */
};

/**
 * @struct type_logic
 * @brief Represents a node in the type logic expression tree.
 *
 * This structure captures information about a node in the type logic expression tree, including its type,
 * data, and pointers to left and right subexpressions.
 */
struct type_logic
{
    enum type_logic_type type; /**< Type of the logic node. */
    union {
        enum type_logic_operator op;        /** ← Logic operator data.                                   */
        struct mpir_ast_identifier* id;     /** ← Identifier data.                                       */
        wchar_t* str_literal;               /** ← String literal data.                                   */
        double num_literal;                 /** ← Numerical literal data.                                */
    } data;                                 /** ← Union of possible data associated with the logic node. */
    struct type_logic* left;                /** ← Pointer to the left subexpression.                     */
    struct type_logic* right;               /** ← Pointer to the right subexpression.                    */
};

/**
 * @struct mpir_ast_type_declaration
 * @brief Represents a type declaration in the Abstract Syntax Tree (AST).
 *
 * This structure captures information about a type declaration, including its identifier, input types,
 * base type, and type refinement logic.
 */
struct mpir_ast_type_declaration
{
    struct mpir_ast_identifier* identifier; /** ← Identifier of the type.               */
    struct mpir_ast_type** inputs;          /** ← Array of input types for the type.    */
    struct mpir_ast_type* base_type;        /** ← Base type of the type.                */
    struct type_logic* refinement;          /** ← Pointer to the type refinement logic. */
};
#endif
