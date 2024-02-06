/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_WJSON_H
#define MPIR_COMPILER_MPIR_WJSON_H

#include <wchar.h>
#include <stdlib.h>
#include <stdio.h>

#include "../../headerbank/mpir_misc/mpir_warnings.h"

/* Forward Declarations */
struct mpir_wjson;
struct mpir_wjson_entry;


typedef union {
    wchar_t value[128];
    struct mpir_wjson* subjson;
    struct mpir_wjson** list;
} mpir_wjson_data;


struct mpir_wjson_entry {
    int is_attribute;
    wchar_t key[128];
    mpir_wjson_data data;
};


struct mpir_wjson {
    struct mpir_wjson_entry** entries;
    int entries_count;
};



struct mpir_wjson* create_wjson();
int wjson_add_attribute(struct mpir_wjson* wjson_node, wchar_t* key, wchar_t* value);
int wjson_add_subwjson(struct mpir_wjson* wjson_node, wchar_t* key, struct mpir_wjson* sub_wjson_node);
int wjson_add_wjsonlist(struct mpir_wjson* wjson_node, wchar_t* key, struct mpir_wjson** list);
int free_wjson(struct mpir_wjson* wjson_node);

// Test function to print mpir_wjson content
void print_wjson(struct mpir_wjson* wjson_node, size_t indentation_level);

void write_wjson_to_file(const wchar_t* file_path, struct mpir_wjson* wjson_node, size_t indentation_level);
void write_wjson_to_file_recursive(FILE* file, struct mpir_wjson* wjson_node, size_t indentation_level);

/* WJson List Stuff */
void wjson_list_free(struct mpir_wjson** list);
void wjson_list_append(struct mpir_wjson** list, struct mpir_wjson* node);
struct mpir_wjson** new_wjson_list();

#endif