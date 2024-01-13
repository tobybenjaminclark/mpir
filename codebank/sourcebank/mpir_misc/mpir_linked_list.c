/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_misc/mpir_linked_list.h"


struct mpir_command_node* create_node(union mpir_command_data data, enum mpir_command_type type) {
    struct mpir_command_node* new_node = (struct mpir_command_node*)malloc(sizeof(struct mpir_command_node));
    new_node->type = type;
    new_node->data = data;
    new_node->next = NULL;
    new_node->prev = NULL;
    return new_node;
}


struct mpir_command_list* initialize_command_list(){
    struct mpir_command_list* list = (struct mpir_command_list*)malloc(sizeof(struct mpir_command_list));
    list->head = NULL;
    list->tail = NULL;
    list->length = 0;
    return list;
}


void append_command(struct mpir_command_list* list, union mpir_command_data data, enum mpir_command_type type) {
    struct mpir_command_node* new_node = create_node(data, type);

    if (list->head == NULL) {
        list->head = new_node;
        list->tail = new_node;
    } else {
        new_node->prev = list->tail;
        list->tail->next = new_node;
        list->tail = new_node;
    }

    list->length++;
}


void free_list(struct mpir_command_list* list) {
    struct mpir_command_node* current = list->head;
    while (current != NULL) {
        struct mpir_command_node* next_node = current->next;
        free(current);
        current = next_node;
    }

    free(list);
}