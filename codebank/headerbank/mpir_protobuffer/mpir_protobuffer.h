/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PROTOBUFFER_H
#define MPIR_COMPILER_MPIR_PROTOBUFFER_H

#include <stdio.h>
#include <stdlib.h>

#include "../../headerbank/mpir_token/mpir_token.h"

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

void test();

#endif
