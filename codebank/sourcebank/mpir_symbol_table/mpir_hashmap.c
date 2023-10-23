/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_symbol_table/mpir_hashmap.h"



/**
 * @brief Hashes a string key to an index within the specified capacity using a simple hash function.
 *
 * This function computes the hash value for the given string key using a simple hash function. It iterates through the characters
 * of the key and calculates the hash value by multiplying the current hash value by 31 and adding the ASCII value of the character.
 * The resulting hash value is then modulo-ed with the specified capacity to obtain an index within the valid range for the hashmap.
 *
 * @param key The string key to be hashed.
 * @param capacity The capacity of the hashmap, used for modulo operation to obtain the index.
 *
 * @return The hashed index within the specified capacity where the key will be placed in the hashmap.
 */

unsigned int mpir_hash(const char* key, int capacity)
{
    unsigned int hash = 0;
    while (*key)
    {
        hash = (hash * 31) + *key;
        key++;
    }
    return hash % capacity;
}



/**
 * @brief Creates a new empty hashmap with an initial capacity, returns NULL if there is an error.
 *
 * This function dynamically allocates memory for a new hashmap structure and its nodes array. If the memory allocation is
 * successful, it initializes the hashmap with the specified initial capacity and sets its size to 0. If memory allocation
 * fails at any step, the function prints a fatal error message and returns a null pointer.
 *
 * @return Pointer to the newly created hashmap if successful, or NULL if memory allocation fails.
 *
 * @note The newly created hashmap is empty, with no key-value pairs. Use mpir_hashmap_put_map or mpir_hashmap_put_value
 * functions to add key-value pairs to the hashmap.
 */
mpir_hashmap* mpir_hashmap_create()
{
    /* Try & allocate memory for the hashmap, in the event of a memory allocation failure, return a null pointer and display a fatal error message. */
    mpir_hashmap* map = (mpir_hashmap*)malloc(sizeof(mpir_hashmap));
    if (map == NULL)
    {
        mpir_fatal("No Remaining Free Memory (Failed to allocate memory for hashmap creation).");
        return NULL;
    }

    /* ry & allocate memory for the nodes, in the event of a memory allocation failure, return a null pointer and display a fatal error message. */
    map->nodes = (mpir_hashnode*)calloc(INITIAL_CAPACITY, sizeof(mpir_hashnode));
    if (map->nodes == NULL)
    {
        mpir_fatal("No Remaining Free Memory (Failed to allocate memory for hashmap nodes creation).");
        return NULL;
    }

    /* Setup initial attributes and return the map. */
    map->capacity = INITIAL_CAPACITY;
    map->size = 0;
    return map;
}



/**
 * @brief Resizes the hashmap by doubling its capacity and rehashing all key-value pairs.
 *
 * This function resizes the hashmap by doubling its capacity and rehashing all existing key-value pairs into the new larger
 * hashmap. It allocates a new block of memory for the hashmap with the increased capacity and re-inserts all key-value pairs
 * using the updated hash function and linear probing. If the resizing is successful, the function updates the hashmap's capacity
 * and nodes array and returns true. If memory allocation for the new hashmap fails, the function prints an error message and returns false.
 *
 * @param map Pointer to the hashmap structure to be resized.
 *
 * @return Returns true if the resizing is successful; otherwise, it returns false, indicating a memory allocation failure.
 */
bool mpir_hashmap_resize(mpir_hashmap* map)
{
    /* Calculate & Allocate new hashmap size. */
    int calculated_capacity = map -> capacity * 2;
    mpir_hashnode* new_nodes = (mpir_hashnode*)calloc(calculated_capacity, sizeof(mpir_hashnode));

    /* Check to ensure memory was successfully allocated. */
    if (new_nodes == NULL)
    {
        mpir_fatal("No Remaining Free Memory (Failed to allocate memory for new hashmap).");
        return false;
    }

    /* Copy across old data to newly allocated block. */
    for (int i = 0; i < map->capacity; ++i)
    {
        /* If no key/value pair, ignore. */
        if (map->nodes[i].key == NULL)
        {
            continue;
        }

        /* If key/value pair, rehash, re-linear-probe and re-insert into the new position. */
        unsigned int index = mpir_hash(map->nodes[i].key, calculated_capacity);
        while (new_nodes[index].key != NULL)
        {
            index = (index + 1) % calculated_capacity;
        }
        new_nodes[index] = map->nodes[i];
    }

    /* Free old map. */
    free(map->nodes);
    map->nodes = new_nodes;
    map->capacity = calculated_capacity;
    return true;
}



/**
 * @brief Inserts a new key-value pair into the hashmap.
 *
 * This function inserts a new key-value pair into the hashmap. If the key already exists in the hashmap, the function does not modify
 * the hashmap and returns false. If the insertion is successful, the function associates the key with the provided value, increasing
 * the size of the hashmap by 1. The hashmap is also resized to double if the size is over the LOAD_FACTOR, this is for amortized
 * optimization across multiple insertions.
 *
 * @param map Pointer to the hashmap structure where the new key-value pair should be inserted.
 * @param key The key to be inserted into the hashmap.
 * @param value The value to be associated with the key in the hashmap.
 *
 * @return Returns true if the insertion is successful, meaning the key did not previously exist in the hashmap; otherwise, it
 * returns false, indicating that the key already exists in the hashmap.
 *
 * @note The function uses linear probing for collision resolution while searching for the appropriate position to insert the key.
 * @note The hashmap is resized if necessary to maintain a load factor below a predefined threshold (LOAD_FACTOR).
 */
bool mpir_hashmap_put_value(mpir_hashmap* map, const char* key, const char* value)
{
    /* Check to see if the hashmap needs resizing. */
    if ((float)(map->size + 1) / map->capacity > LOAD_FACTOR)
    {
        mpir_hashmap_resize(map);
    }

    /* Calculate the index to insert at from the hash function. */
    unsigned int index = mpir_hash(key, map->capacity);

    /* Check the position to insert at using linear probing. */
    while (map->nodes[index].key != NULL)
    {
        if (strcmp(map->nodes[index].key, key) == 0)
        {
            /* Key already exists, return false. */
            return false;
        }
        index = (index + 1) % map->capacity;
    }

    /* Insert new key-value pair & update hashmap data. */
    map->nodes[index].key = strdup(key);
    map->nodes[index].data.value = strdup(value);
    map->size++;
    return true;
}



/**
 * @brief Inserts a new key into the hashmap with an associated empty nested hashmap.
 *
 * This function inserts a new key into the hashmap and associates it with an empty nested hashmap. If the key already exists in the
 * hashmap, the function does not modify the hashmap and returns false. If the insertion is successful, the function creates an empty
 * nested hashmap and associates it with the key, increasing the size of the hashmap by 1. The hashmap is also resized to double if
 * the size is over the LOAD_FACTOR, this is for amortized optimization across multiple insertions.
 *
 * @param map Pointer to the hashmap structure where the new key and nested hashmap should be inserted.
 * @param key The key to be inserted into the hashmap.
 *
 * @return Returns true if the insertion is successful, meaning the key did not previously exist in the hashmap; otherwise, it
 * returns false, indicating that the key already exists in the hashmap.
 *
 * @note The function uses linear probing for collision resolution while searching for the appropriate position to insert the key.
 * @note The hashmap is resized if necessary to maintain a load factor below a predefined threshold (LOAD_FACTOR).
 */
bool mpir_hashmap_put_map(mpir_hashmap* map, const char* key)
{
    /* Check to see if the hashmap needs resizing. */
    if ((float)(map->size + 1) / map->capacity > LOAD_FACTOR)
    {
        mpir_hashmap_resize(map);
    }

    /* Calculate the index to insert at from the hash function. */
    unsigned int index = mpir_hash(key, map->capacity);

    /* Check the position to insert at using linear probing. */
    while (map->nodes[index].key != NULL)
    {
        if (strcmp(map->nodes[index].key, key) == 0)
        {
            /* Key already exists, return the existing map */
            return false;
        }
        index = (index + 1) % map->capacity;
    }

    /* Insert new key-map pair & update hashmap data. */
    map->nodes[index].key = strdup(key);
    map->nodes[index].is_map = 1;
    map->nodes[index].data.map = mpir_hashmap_create();
    map->size++;
    return true;
}



/**
 * @brief Retrieves the value associated with a specified key from the hashmap.
 *
 * This function searches for the specified key in the hashmap and returns the associated value if found. If the key is found
 * and maps to a nested hashmap, it returns a special message indicating that it is not printable.
 *
 * @param map Pointer to the hashmap structure to search within.
 * @param key The key to look for in the hashmap.
 *
 * @return If the key is found and maps to a simple value, the function returns a pointer to the value (string) associated with
 * the key. If the key is found and maps to a nested hashmap, the function returns a special message indicating that it is not
 * printable. If the key is not found, the function returns NULL.
 *
 * @note The function uses linear probing for collision resolution while searching for the key.
 * @note If the returned value is "Nested mpir_hashmap (not printable)", it means the key maps to a nested hashmap,
 * and further details about the nested hashmap are not available through this function.
 */
const char* mpir_hashmap_get_value(mpir_hashmap* map, const char* key)
{
    /* Perform the hash-operation on the key, to calculate the index. */
    unsigned int index = mpir_hash(key, map -> capacity);
    while (map -> nodes[index].key != NULL)
    {
        /* If the found key is not equal to the passed key, then increment and try again. (Linear probing appraoch). */
        if (strcmp(map -> nodes[index].key, key) == 1)
        {
            /* If the key, value pair was not found, increment the index and research (linear probe) */
            index = (index + 1) % map -> capacity;
            continue;
        }

        /* If it's a map, then return NULL and display an error. */
        if (map -> nodes[index].is_map)
        {
            mpir_warn("Failure in attempting to retrieve value, key: %s as value, value is mpir_hashmap.", key);
            return NULL;
        }

        /* If it's a value, return it and exit the function. */
        else
        {
            return map -> nodes[index].data.value;
        }
    }

    /* No associated value for key found, show warning message. */
    mpir_warn("Failure in attempting to retrieve value, no value exists for key: %s.", key);
    return NULL;
}



/**
 * @brief Frees the memory occupied by a hashmap and its associated data recursively.
 *
 * This function deallocates the memory used by the given hashmap and its contents. It iterates through each key-value pair
 * in the hashmap, freeing the keys, values, and nested hashmaps if present. It also frees the array of nodes in the hashmap.
 * Basic iterative/recursive approach, frees the hashmap in O(n).
 *
 * @param map Pointer to the hashmap structure to be freed.
 * @note After calling this function, the provided hashmap pointer becomes invalid and should not be accessed.
 * @warning Ensure that the hashmap and its contents are no longer in use before calling this function to avoid memory leaks.
 */

void mpir_hashmap_free(mpir_hashmap* map)
{
    /* Iterate through each key, value pair in the hashmap, freeing the value or making a recursive call. */
    for (int i = 0; i < map -> capacity; ++i)
    {
        /* Ensures there is a record to 'free' */
        if (map->nodes[i].key == NULL)
        {
            continue;
        }

        /* Free the value of the key */
        free(map -> nodes[i].key);

        /* Recursive call (if value is a hashmap) */
        if (map -> nodes[i].is_map)
        {
            (void)mpir_hashmap_free(map->nodes[i].data.map);
        }

        /* Base Case (Value is data) */
        else
        {
            (void)free(map->nodes[i].data.value);
        }
    }

    /* Free the array, then the struct itself. */
    free(map->nodes);
    free(map);
}



/**
 * @brief Recursively prints the contents of a hashmap with a specified indentation level.
 *
 * This function iterates through the hashmap and prints its key-value pairs. If a key maps to another hashmap,
 * it recursively prints the nested hashmap with increased indentation level.
 *
 * @param map Pointer to the hashmap structure to be printed.
 * @param indentation The current level of nesting, used for indentation in the output.
 *
 * @note This function assumes that the hashmap has been properly initialized and contains valid data.
 * @warning Ensure that the hashmap is not modified while this function is executing to avoid unexpected behavior.
 */

void mpir_hashmap_display_internal(mpir_hashmap* map, int indentation)
{
    /* Iterate through every record in the hashmap, as we are going to display the value/hashmap in each of these. */
    for (int i = 0; i < map->capacity; ++i)
    {
        /* If the node is null, we can skip it. */
        if (map -> nodes[i].key == NULL){continue;}

        /* Indent the output dependent on the depth (i.e. sub-maps will be indented more than surface level values). */
        for (int j = 0; j < indentation; ++j){printf("  ");}

        /* Display the key value (string) */
        printf("\"%s\": ", map->nodes[i].key);

        /* If the value is a nested hashmap (recursive call) */
        if (map->nodes[i].is_map)
        {
            /* If nested hashmap, print recursively with increased indentation level */
            printf("{\n");
            mpir_hashmap_display_internal(map->nodes[i].data.map, indentation + 1);

            /* Print indentation for closing curly brace */
            for (int j = 0; j < indentation; ++j){printf("  ");}

            printf("}\n");
        }

            /* If the map is a value, display it (base-case). */
        else if(!(map -> nodes[i].is_map))
        {
            printf("\"%s\"\n", map->nodes[i].data.value);
        }
    }
}



/**
 * @brief Wrapper for mpir_hashmap_display_internal()
 *
 * This function is a wrapper for the mpir_hashmap_display_internal() function, which recursively
 * displays a nested hashmap's key-value pairs to stdout. Use this function to print the hashmap,
 * as it sets the initial indentation level (unless you need to do this yourself?)
 *
 * @param map Pointer to the hashmap structure to be displayed.
 * @note This function assumes that the hashmap has been properly initialized and contains valid data.
 */
void mpir_hashmap_display(mpir_hashmap* map)
{
    mpir_hashmap_display_internal(map, 0);
}

