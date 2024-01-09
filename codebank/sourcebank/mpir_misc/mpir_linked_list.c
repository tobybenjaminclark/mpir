/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_misc/mpir_linked_list.h"

// Function to create a new node with the given data
struct mpir_command_node* create_node(union command_data data) {
    struct mpir_command_node* new_node = (struct mpir_command_node*)malloc(sizeof(struct mpir_command_node));
    new_node->data = data;
    new_node->next = NULL;
    new_node->prev = NULL;
    return new_node;
}

// Function to initialize a new doubly linked list
struct mpir_command_list* initialize_list(){
    struct mpir_command_list* list = (struct mpir_command_list*)malloc(sizeof(struct mpir_command_list));
    list->head = NULL;
    list->tail = NULL;
    list->length = 0;
    return list;
}

// Function to insert a new node at the end of the doubly linked list
void insert_at_end(struct mpir_command_list* list, union command_data data) {
    struct mpir_command_node* new_node = create_node(data);

    if (list->head == NULL) {
        list->head = new_node;
        list->tail = new_node;
    } else {
        new_node->prev = list->tail;
        list->tail->next = new_node;
        list->tail = new_node;
    }

    list->length++;

    printf("added to list, new length is %d \n", list->length);
}

// Function to free the memory allocated for the doubly linked list
void free_list(struct mpir_command_list* list) {
    struct mpir_command_node* current = list->head;
    while (current != NULL) {
        struct mpir_command_node* next_node = current->next;
        free(current);
        current = next_node;
    }

    free(list);
}