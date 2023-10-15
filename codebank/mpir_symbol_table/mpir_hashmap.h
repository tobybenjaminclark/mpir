#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../mpir_logging/mpir_warnings.h"

#define INITIAL_CAPACITY 16
#define LOAD_FACTOR 0.7

typedef struct {
    char* key;
    union {
        char* value;
        struct mpir_hashmap* map;
    } data;
    int is_map;
} mpir_hashnode;

typedef struct mpir_hashmap {
    mpir_hashnode* nodes;
    int capacity;
    int size;
} mpir_hashmap;

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
const char* mpir_hashmap_get(mpir_hashmap* map, const char* key);

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