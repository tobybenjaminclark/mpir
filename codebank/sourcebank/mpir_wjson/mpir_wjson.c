/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_wjson/mpir_wjson.h"

// Function to create an empty mpir_wjson
struct mpir_wjson* create_wjson()
{
    struct mpir_wjson* wjson_node = malloc(sizeof(struct mpir_wjson));
    if (wjson_node == NULL)
    {
        mpir_fatal("wJSON: Out of Memory");
        return NULL;
    }

    wjson_node->entries = NULL;
    wjson_node->entries_count = 0;
    return wjson_node;
}

// Function to add a simple attribute (wchar_t value) to the mpir_wjson
int wjson_add_attribute(struct mpir_wjson* wjson_node, wchar_t* key, wchar_t* value)
{
    if (wjson_node == NULL || key == NULL || value == NULL)
    {
        mpir_fatal("wJSON: Invalid Input");
        return -1;
    }

    // Allocate memory for the new entry
    struct mpir_wjson_entry* new_entry = malloc(sizeof(struct mpir_wjson_entry));
    if (new_entry == NULL)
    {
        mpir_fatal("wJSON: Out of Memory");
        return -1;
    }

    // Copy key and value into the new entry
    wcsncpy(new_entry->key, key, 128);
    wcsncpy(new_entry->data.value, value, 128);
    new_entry->is_attribute = 1;

    // Reallocate memory for entries array
    wjson_node->entries = realloc(wjson_node->entries, (wjson_node->entries_count + 1) * sizeof(struct mpir_wjson_entry*));
    if (wjson_node->entries == NULL)
    {
        mpir_fatal("wJSON: Out of Memory");
        free(new_entry);
        return -1;
    }

    // Add the new entry to the array
    wjson_node->entries[wjson_node->entries_count] = new_entry;
    wjson_node->entries_count++;

    return 0;
}

// Function to add a subjson to the mpir_wjson
int wjson_add_subwjson(struct mpir_wjson* wjson_node, wchar_t* key, struct mpir_wjson* sub_wjson_node) {
    if (wjson_node == NULL || key == NULL || sub_wjson_node == NULL)
    {
        // Invalid input
        return -1;
    }

    // Allocate memory for the new entry
    struct mpir_wjson_entry* new_entry = malloc(sizeof(struct mpir_wjson_entry));
    if (new_entry == NULL)
    {
        // Allocation failed
        return -1;
    }

    // Copy key and subjson into the new entry
    wcsncpy(new_entry->key, key, 128);
    new_entry->data.subjson = sub_wjson_node;
    new_entry->is_attribute = 0;

    // Reallocate memory for entries array
    wjson_node->entries = realloc(wjson_node->entries, (wjson_node->entries_count + 1) * sizeof(struct mpir_wjson_entry*));
    if (wjson_node->entries == NULL)
    {
        // Allocation failed
        free(new_entry);
        return -1;
    }

    // Add the new entry to the array
    wjson_node->entries[wjson_node->entries_count] = new_entry;
    wjson_node->entries_count++;

    return 0;
}

int wjson_add_wjsonlist(struct mpir_wjson* wjson_node, wchar_t* key, struct mpir_wjson** list)
{
    /* Validate Inputs */
    if (wjson_node == NULL || key == NULL || list == NULL)
    {
        mpir_fatal("wJSON: Invalid Input");
        return -1;
    }

    // Allocate memory for the new entry
    struct mpir_wjson_entry* new_entry = malloc(sizeof(struct mpir_wjson_entry));
    if (new_entry == NULL)
    {
        mpir_fatal("wJSON: Out of Memory");
        return -1;
    }

    // Copy key and value into the new entry
    wcsncpy(new_entry->key, key, 128);
    new_entry->data.list = list;
    new_entry->is_attribute = 1;

    // Reallocate memory for entries array
    wjson_node->entries = realloc(wjson_node->entries, (wjson_node->entries_count + 1) * sizeof(struct mpir_wjson_entry*));
    if (wjson_node->entries == NULL)
    {
        mpir_fatal("wJSON: Out of Memory");
        free(new_entry);
        return -1;
    }

    // Add the new entry to the array
    wjson_node->entries[wjson_node->entries_count] = new_entry;
    wjson_node->entries_count++;

    return 0;
}



// Function to free the memory allocated for mpir_wjson
int free_wjson(struct mpir_wjson* wjson_node) {
    if (wjson_node == NULL)
    {
        // Nothing to free
        return 0;
    }

    for (size_t i = 0; i < wjson_node->entries_count; i++)
    {
        free(wjson_node->entries[i]);
    }

    free(wjson_node->entries);
    free(wjson_node);

    return 0;
}

// Test function to print mpir_wjson content
void print_wjson(struct mpir_wjson* wjson_node, size_t indentation_level)
{
    if (wjson_node == NULL) {
        printf("NULL\n");
        return;
    }

    printf("{\n");
    for (size_t i = 0; i < wjson_node->entries_count; i++)
    {
        // Indentation
        for (size_t j = 0; j <= indentation_level; j++) {
            printf("  ");
        }

        printf("\"%ls\": ", wjson_node->entries[i]->key);
        if (wjson_node->entries[i]->is_attribute == 0)
        {
            print_wjson(wjson_node->entries[i]->data.subjson, indentation_level + 1);
        }
        else
        {
            wprintf(L"\"%ls\"\n", wjson_node->entries[i]->data.value);
        }
    }

    // Closing brace indentation
    for (size_t j = 0; j < indentation_level; j++) {
        printf("  ");
    }

    printf("}\n");
}


void write_wjson_to_file(const wchar_t* file_path, struct mpir_wjson* wjson_node, size_t indentation_level)
{
    FILE* file = fopen(file_path, L"w");

    if (file == NULL) {
        wprintf(L"Error opening file: %ls\n", file_path);
        return;
    }

    if (wjson_node == NULL) {
        fwprintf(file, L"NULL\n");
    } else {
        write_wjson_to_file_recursive(file, wjson_node, indentation_level);
    }

    fclose(file);
}

// Helper function for recursive writing
void write_wjson_to_file_recursive(FILE* file, struct mpir_wjson* wjson_node, size_t indentation_level)
{
    fwprintf(file, L"{\n");
    for (size_t i = 0; i < wjson_node->entries_count; i++)
    {
        // Indentation
        for (size_t j = 0; j <= indentation_level; j++) {
            fwprintf(file, L"  ");
        }

        fwprintf(file, L"\"%ls\": ", wjson_node->entries[i]->key);
        if (wjson_node->entries[i]->is_attribute == 0)
        {
            write_wjson_to_file_recursive(file, wjson_node->entries[i]->data.subjson, indentation_level + 1);
        }
        else
        {
            fwprintf(file, L"\"%ls\"\n", wjson_node->entries[i]->data.value);
        }
    }

    // Closing brace indentation
    for (size_t j = 0; j < indentation_level; j++) {
        fwprintf(file, L"  ");
    }

    fwprintf(file, L"}\n");
}


void wjson_list_free(struct mpir_wjson** list) {
    struct mpir_wjson* current = *list;
    struct mpir_wjson* next;

    // Free each entry in the list
    while (current != NULL) {
        next = current->entries;
        free(current);
        current = next;
    }

    // Free the list itself
    free(list);
}

void wjson_list_append(struct mpir_wjson** list, struct mpir_wjson* node) {
    // Reallocate memory for a new node in the list
    (*list)->entries = (struct mpir_wjson_entry**)realloc((*list)->entries, ((*list)->entries_count + 1) * sizeof(struct mpir_wjson_entry*));

    if ((*list)->entries == NULL) {
        fprintf(stderr, "Memory allocation error for wjson_list_append\n");
        exit(EXIT_FAILURE);
    }

    // Allocate memory for a new entry in the list
    struct mpir_wjson_entry* new_entry = (struct mpir_wjson_entry*)malloc(sizeof(struct mpir_wjson_entry));

    if (new_entry == NULL) {
        fprintf(stderr, "Memory allocation error for wjson_list_append\n");
        exit(EXIT_FAILURE);
    }

    // Set the new entry's data to the provided node
    new_entry->data.list = node;

    // Update the list's entries to point to the new entry
    (*list)->entries[(*list)->entries_count++] = new_entry;
}

struct mpir_wjson** new_wjson_list() {
    // Allocate memory for the list
    struct mpir_wjson** list = (struct mpir_wjson**)malloc(sizeof(struct mpir_wjson*));

    if (list == NULL)
    {
        fprintf(stderr, "Memory allocation error for new_wjson_list\n");
        exit(EXIT_FAILURE);
    }

    // Initialize the list with a NULL pointer
    *list = (struct mpir_wjson*)malloc(sizeof(struct mpir_wjson));
    if (*list == NULL)
    {
        fprintf(stderr, "Memory allocation error for new_wjson_list\n");
        exit(EXIT_FAILURE);
    }

    // Initialize the entries_count to 0
    (*list)->entries_count = 0;
    // Initialize entries to NULL
    (*list)->entries = NULL;

    return list;
}
