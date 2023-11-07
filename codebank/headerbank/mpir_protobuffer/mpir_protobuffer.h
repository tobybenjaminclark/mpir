/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PROTOBUFFER_H
#define MPIR_COMPILER_MPIR_PROTOBUFFER_H

#include <stdio.h>
#include <stdlib.h>
#include <locale.h>
#include <wchar.h>
#include <stdbool.h>

#include "../../headerbank/mpir_token/mpir_token.h"

/* Macro for protobuffer file not found error message */
#define MPIR_PB_FNF "mpir_protobuffer: failed to open file %s"

/* Macro to initialize a specific field within a struct instance */
#define INIT_FIELD(struct_instance, field_name, value) \
        (struct_instance)->field_name = value; \

/* Macro to create a struct instance */
#define CREATE_STRUCT(struct_type, instance_name) \
        struct_type* instance_name = (struct_type*)malloc(sizeof(struct_type)); \

/* Macro to create a struct instance and initialize a specific field */
#define CREATE_AND_INIT_STRUCT(struct_type, field_name, value) \
    ({ \
        struct_type* instance = (struct_type*)malloc(sizeof(struct_type)); \
        if (instance != NULL) { \
            instance->field_name = value; \
        } \
        instance; \
    })

#define PB_BUFFER_SIZE 128

struct mpir_protobuffer_template
{
    wchar_t template_name[128];
    wchar_t* types[128];
    wchar_t* identifiers[128];
};

typedef enum
{
    AWAITING_STRUCTURE,
    PARSING_STRUCTURE,
    AWAITING_TYPE,
    PARSING_MEMBER_TYPE,
    AWAITING_IDENTIFIER,
    PARSING_MEMBER_IDENTIFIER,
    DETECT_IF_END
} mpir_protobuffer_template_parser_state;

int mpir_protobuffer_allocate_new_template(struct mpir_protobuffer_template*** templates, int* number_of_templates);
FILE* mpir_protobuffer_open_file(const char* file_path);
int mpir_parse_protobuffer_template(const wchar_t* file_path);
void test();

#endif
