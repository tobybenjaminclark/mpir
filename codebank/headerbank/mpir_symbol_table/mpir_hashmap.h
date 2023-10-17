//
// Created by Toby Benjamin Clark on 16/10/2023.
//

#ifndef UNTITLED_MPIR_HASHMAP_H
#define UNTITLED_MPIR_HASHMAP_H

#include "../mpir_misc/mpir_warnings.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>



/// @brief The initial capacity of a hashmap when it is created.
///
/// This macro defines the initial number of slots in the hashmap's array of nodes when a new hashmap is created.
#define INITIAL_CAPACITY 16



/// @brief The load factor threshold for resizing the hashmap.
///
/// This macro defines the threshold for the load factor, which is the ratio of the number of elements to the capacity of the hashmap.
/// If the load factor exceeds this value, the hashmap is resized to maintain efficiency.
#define LOAD_FACTOR 0.7



/// @brief Represents a node in the hashmap containing key-value pair or nested hashmap reference.
///
/// Each node in the hashmap contains a key, and a union that can hold either a simple string value or a pointer to another
/// hashmap structure. The 'is_map' flag indicates whether the node contains a nested hashmap or a simple string value.
///
typedef struct {
    char* key;  ///< The key associated with the node.
    union {
        char* value;                ///< Pointer to the string value associated with the key.
        struct mpir_hashmap* map;   ///< Pointer to the nested hashmap associated with the key.
    } data;                         ///< Union to hold either a string value or a pointer to another hashmap.
    int is_map;                     ///< Flag indicating whether the node contains a nested hashmap (1) or a string value (0).
} mpir_hashnode;



/// @brief Represents a hashmap data structure.
///
/// The hashmap structure contains an array of nodes (mpir_hashnode) which store key-value pairs or references to nested hashmaps.
/// It also tracks the current capacity of the hashmap and the number of elements stored in it (size).
typedef struct {
    mpir_hashnode* nodes;           ///< Pointer to an array of hash nodes storing key-value pairs or references to nested hashmaps.
    int capacity;                   ///< The current capacity of the hashmap (size of the nodes array).
    int size;                       ///< The number of elements currently stored in the hashmap.
} mpir_hashmap;



/// @brief Hashes a string key to an index within the specified capacity using a simple hash function.
///
/// This function computes the hash value for the given string key using a simple hash function. It iterates through the characters
/// of the key and calculates the hash value by multiplying the current hash value by 31 and adding the ASCII value of the character.
/// The resulting hash value is then modulo-ed with the specified capacity to obtain an index within the valid range for the hashmap.
///
/// @param key The string key to be hashed.
/// @param capacity The capacity of the hashmap, used for modulo operation to obtain the index.
///
/// @return The hashed index within the specified capacity where the key will be placed in the hashmap.
unsigned int mpir_hash(const char* key, int capacity);



/// @brief Creates a new empty hashmap with an initial capacity, returns NULL if there is an error.
///
/// This function dynamically allocates memory for a new hashmap structure and its nodes array. If the memory allocation is
/// successful, it initializes the hashmap with the specified initial capacity and sets its size to 0. If memory allocation
/// fails at any step, the function prints a fatal error message and returns a null pointer.
///
/// @return Pointer to the newly created hashmap if successful, or NULL if memory allocation fails.
///
/// @note The newly created hashmap is empty, with no key-value pairs. Use mpir_hashmap_put_map or mpir_hashmap_put_value
/// functions to add key-value pairs to the hashmap.
mpir_hashmap* mpir_hashmap_create();



/// @brief Resizes the hashmap by doubling its capacity and rehashing all key-value pairs.
///
/// This function resizes the hashmap by doubling its capacity and rehashing all existing key-value pairs into the new larger
/// hashmap. It allocates a new block of memory for the hashmap with the increased capacity and re-inserts all key-value pairs
/// using the updated hash function and linear probing. If the resizing is successful, the function updates the hashmap's capacity
/// and nodes array and returns true. If memory allocation for the new hashmap fails, the function prints an error message and returns false.
///
/// @param map Pointer to the hashmap structure to be resized.
///
/// @return Returns true if the resizing is successful; otherwise, it returns false, indicating a memory allocation failure.
bool mpir_hashmap_resize(mpir_hashmap* map);



/// @brief Inserts a new key-value pair into the hashmap.
///
/// This function inserts a new key-value pair into the hashmap. If the key already exists in the hashmap, the function does not modify
/// the hashmap and returns false. If the insertion is successful, the function associates the key with the provided value, increasing
/// the size of the hashmap by 1. The hashmap is also resized to double if the size is over the LOAD_FACTOR, this is for amortized
/// optimization across multiple insertions.
///
/// @param map Pointer to the hashmap structure where the new key-value pair should be inserted.
/// @param key The key to be inserted into the hashmap.
/// @param value The value to be associated with the key in the hashmap.
///
/// @return Returns true if the insertion is successful, meaning the key did not previously exist in the hashmap; otherwise, it
/// returns false, indicating that the key already exists in the hashmap.
///
/// @note The function uses linear probing for collision resolution while searching for the appropriate position to insert the key.
/// @note The hashmap is resized if necessary to maintain a load factor below a predefined threshold (LOAD_FACTOR).
bool mpir_hashmap_put_value(mpir_hashmap* map, const char* key, const char* value);



/// @brief Inserts a new key into the hashmap with an associated empty nested hashmap.
///
/// This function inserts a new key into the hashmap and associates it with an empty nested hashmap. If the key already exists in the
/// hashmap, the function does not modify the hashmap and returns false. If the insertion is successful, the function creates an empty
/// nested hashmap and associates it with the key, increasing the size of the hashmap by 1. The hashmap is also resized to double if
/// the size is over the LOAD_FACTOR, this is for amortized optimization across multiple insertions.
///
/// @param map Pointer to the hashmap structure where the new key and nested hashmap should be inserted.
/// @param key The key to be inserted into the hashmap.
///
/// @return Returns true if the insertion is successful, meaning the key did not previously exist in the hashmap; otherwise, it
/// returns false, indicating that the key already exists in the hashmap.
///
/// @note The function uses linear probing for collision resolution while searching for the appropriate position to insert the key.
/// @note The hashmap is resized if necessary to maintain a load factor below a predefined threshold (LOAD_FACTOR).
bool mpir_hashmap_put_map(mpir_hashmap* map, const char* key);



/// @brief Retrieves the value associated with a specified key from the hashmap.
///
/// This function searches for the specified key in the hashmap and returns the associated value if found. If the key is found
/// and maps to a nested hashmap, it returns a special message indicating that it is not printable.
///
/// @param map Pointer to the hashmap structure to search within.
/// @param key The key to look for in the hashmap.
///
/// @return If the key is found and maps to a simple value, the function returns a pointer to the value (string) associated with
/// the key. If the key is found and maps to a nested hashmap, the function returns a special message indicating that it is not
/// printable. If the key is not found, the function returns NULL.
///
/// @note The function uses linear probing for collision resolution while searching for the key.
/// @note If the returned value is "Nested mpir_hashmap (not printable)", it means the key maps to a nested hashmap,
/// and further details about the nested hashmap are not available through this function.
///
const char* mpir_hashmap_get_value(mpir_hashmap* map, const char* key);



/// @brief Frees the memory occupied by a hashmap and its associated data recursively.
///
/// This function deallocates the memory used by the given hashmap and its contents. It iterates through each key-value pair
/// in the hashmap, freeing the keys, values, and nested hashmaps if present. It also frees the array of nodes in the hashmap.
/// Basic iterative/recursive approach, frees the hashmap in O(n).
///
/// @param map Pointer to the hashmap structure to be freed.
/// @note After calling this function, the provided hashmap pointer becomes invalid and should not be accessed.
/// @warning Ensure that the hashmap and its contents are no longer in use before calling this function to avoid memory leaks.
void mpir_hashmap_free(mpir_hashmap* map);



/// @brief Recursively prints the contents of a hashmap with a specified indentation level.
///
/// This function iterates through the hashmap and prints its key-value pairs. If a key maps to another hashmap,
/// it recursively prints the nested hashmap with increased indentation level.
///
/// @param map Pointer to the hashmap structure to be printed.
/// @param indentation The current level of nesting, used for indentation in the output.
///
/// @note This function assumes that the hashmap has been properly initialized and contains valid data.
/// @warning Ensure that the hashmap is not modified while this function is executing to avoid unexpected behavior.
///
void mpir_hashmap_display_internal(mpir_hashmap* map, int indentation);



/// @brief Wrapper for mpir_hashmap_display_internal()
///
/// This function is a wrapper for the mpir_hashmap_display_internal() function, which recursively
/// displays a nested hashmaps key, value pairs to stdout. Use this function to print the hashmap,
/// as it sets the initial indentation level (unless you need to do this yourself?)
///
/// @param map Pointer to the hashmap structure to be displayed.
/// @note This function assumes that the hashmap has been properly initialized and contains valid data.
///
void mpir_hashmap_display(mpir_hashmap* map);

#endif //UNTITLED_MPIR_HASHMAP_H
