/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_misc/mpir_definition_list.h"


struct mpir_declaration_node* create_declaration_node(union mpir_declaration_data data) {
    struct mpir_declaration_node* new_node = (struct mpir_command_node*)malloc(sizeof(struct mpir_declaration_node));
    new_node->data = data;
    new_node->next = NULL;
    new_node->prev = NULL;
    return new_node;
}


struct mpir_declaration_list* initialize_declaration_list(){
    struct mpir_declaration_list* list = (struct mpir_command_list*)malloc(sizeof(struct mpir_declaration_list));
    list->head = NULL;
    list->tail = NULL;
    list->length = 0;
    return list;
}


void add_declaration(struct mpir_declaration_list* list, union mpir_declaration_data data) {
    struct mpir_declaration_node* new_node = create_declaration_node(data);

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


void free_declaration_list(struct mpir_declaration_list* list) {
    struct mpir_declaration_node* current = list->head;
    while (current != NULL) {
        struct mpir_declaration_node* next_node = current->next;
        free(current);
        current = next_node;
    }

    free(list);
}