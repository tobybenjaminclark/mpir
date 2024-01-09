/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_misc/mpir_linked_list.h"

// Function to create a new node with the given data
struct command_node* create_node(union command_data data) {
    struct command_node* new_node = (struct command_node*)malloc(sizeof(struct command_node));
    new_node->data = data;
    new_node->next = NULL;
    new_node->prev = NULL;
    return new_node;
}

// Function to insert a new node at the end of the doubly linked list
void insert_at_end(struct command_node** head, union command_data data) {
    struct command_node* new_node = create_node(data);

    if (*head == NULL) {
        *head = new_node;
    } else {
        struct command_node* current = *head;
        while (current->next != NULL) {
            current = current->next;
        }

        current->next = new_node;
        new_node->prev = current;
    }
}

// Function to free the memory allocated for the doubly linked list
void free_list(struct command_node* head) {
    struct command_node* current = head;
    while (current != NULL) {
        struct command_node* next_node = current->next;
        free(current);
        current = next_node;
    }
}

int main() {
    struct command_node* head = NULL;

    // Inserting elements into the doubly linked list with different data types
    insert_at_end(&head, (union command_data){.intValue = 1});
    insert_at_end(&head, (union command_data){.floatValue = 2.5});
    insert_at_end(&head, (union command_data){.stringValue = "Hello"});


    return 0;
}