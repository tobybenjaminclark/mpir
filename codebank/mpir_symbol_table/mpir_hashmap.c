#include "../mpir_symbol_table/mpir_hashmap.h"

unsigned int mpir_hash(const char* key, int capacity) {
    unsigned int hash = 0;
    while (*key) {
        hash = (hash * 31) + *key;
        key++;
    }
    return hash % capacity;
}

mpir_hashmap* mpir_hashmap_create() {
    mpir_hashmap* map = (mpir_hashmap*)malloc(sizeof(mpir_hashmap));
    if (map == NULL) {
        perror("Memory allocation error");
        exit(EXIT_FAILURE);
    }

    map->nodes = (mpir_hashnode*)calloc(INITIAL_CAPACITY, sizeof(mpir_hashnode));
    if (map->nodes == NULL) {
        perror("Memory allocation error");
        exit(EXIT_FAILURE);
    }

    map->capacity = INITIAL_CAPACITY;
    map->size = 0;
    return map;
}

void mpir_hashmap_resize(mpir_hashmap* map) {
    int newCapacity = map->capacity * 2;
    mpir_hashnode* newNodes = (mpir_hashnode*)calloc(newCapacity, sizeof(mpir_hashnode));
    if (newNodes == NULL) {
        perror("Memory allocation error");
        exit(EXIT_FAILURE);
    }

    for (int i = 0; i < map->capacity; ++i) {
        if (map->nodes[i].key != NULL) {
            unsigned int index = mpir_hash(map->nodes[i].key, newCapacity);
            while (newNodes[index].key != NULL) {
                index = (index + 1) % newCapacity;
            }
            newNodes[index] = map->nodes[i];
        }
    }

    free(map->nodes);
    map->nodes = newNodes;
    map->capacity = newCapacity;
}

void mpir_hashmap_put_value(mpir_hashmap* map, const char* key, const char* value) {
    if ((float)(map->size + 1) / map->capacity > LOAD_FACTOR) {
        mpir_hashmap_resize(map);
    }

    unsigned int index = mpir_hash(key, map->capacity);
    while (map->nodes[index].key != NULL) {
        if (strcmp(map->nodes[index].key, key) == 0) {
            // Key already exists, update the value
            free(map->nodes[index].data.value);
            map->nodes[index].data.value = strdup(value);
            return;
        }
        index = (index + 1) % map->capacity;
    }

    // Insert new key-value pair
    map->nodes[index].key = strdup(key);
    map->nodes[index].data.value = strdup(value);
    map->size++;
}

mpir_hashmap* mpir_hashmap_put_map(mpir_hashmap* map, const char* key) {
    if ((float)(map->size + 1) / map->capacity > LOAD_FACTOR) {
        mpir_hashmap_resize(map);
    }

    unsigned int index = mpir_hash(key, map->capacity);
    while (map->nodes[index].key != NULL) {
        if (strcmp(map->nodes[index].key, key) == 0) {
            // Key already exists, return the existing map
            return map->nodes[index].data.map;
        }
        index = (index + 1) % map->capacity;
    }

    // Insert new key-map pair
    map->nodes[index].key = strdup(key);
    map->nodes[index].is_map = 1;
    map->nodes[index].data.map = mpir_hashmap_create();
    map->size++;
    return map->nodes[index].data.map;
}

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
const char* mpir_hashmap_get_value(mpir_hashmap* map, const char* key)
{
    // Perform the hash-operation on the key, to calculate the index.
    unsigned int index = mpir_hash(key, map -> capacity);
    while (map -> nodes[index].key != NULL)
    {
        // If the found key is not equal to the passed key, then increment
        // and try again. (Linear probing appraoch).
        if (strcmp(map -> nodes[index].key, key) == 1)
        {
            // If the key, value pair was not found, increment the index and
            // re-search (linear probe the hash map.)
            index = (index + 1) % map -> capacity;
            continue;
        }

        // If it's a map, then return NULL and display an error.
        if (map -> nodes[index].is_map)
        {
            mpir_warn("Failure in attempting to retrieve value, key: %s as value, value is mpir_hashmap.", key);
            return NULL;
        }
        
        // If it's a value, return it and exit the function.
        else
        {
            return map -> nodes[index].data.value;
        }
    }

    // No associated value for key found, show warning message.
    mpir_warn("Failure in attempting to retrieve value, no value exists for key: %s.", key);
    return NULL;
}

/// @brief Frees the memory occupied by a hashmap and its associated data recursively.
///
/// This function deallocates the memory used by the given hashmap and its contents. It iterates through each key-value pair
/// in the hashmap, freeing the keys, values, and nested hashmaps if present. It also frees the array of nodes in the hashmap.
/// Basic iterative/recursive approach, frees the hashmap in O(n).
///
/// @param map Pointer to the hashmap structure to be freed.
/// @note After calling this function, the provided hashmap pointer becomes invalid and should not be accessed.
/// @warning Ensure that the hashmap and its contents are no longer in use before calling this function to avoid memory leaks.
void mpir_hashmap_free(mpir_hashmap* map)
{
    // Iterate through each key, value pair in the hashmap, freeing the value
    // or making a recursive call.
    for (int i = 0; i < map -> capacity; ++i)
    {
        // Ensures there is a record to 'free'
        if (map->nodes[i].key == NULL)
        {
            continue;
        }
        // Free the value of the key
        free(map -> nodes[i].key);

        // Recursive call (if value is a hashmap)
        if (map -> nodes[i].is_map)
        {
            (void)mpir_hashmap_free(map->nodes[i].data.map);
        }

        // Base case (value is data)
        else
        {
            (void)free(map->nodes[i].data.value);
        }
    }
    
    // Free the array, then the struct itself.
    free(map->nodes);
    free(map);
}

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
void mpir_hashmap_display_internal(mpir_hashmap* map, int indentation)
{
    // Iterate through every record in the hashmap, as we are going to
    // display the value/hashmap in each of these.
    for (int i = 0; i < map->capacity; ++i)
    {
        // If the node is null, we can skip it.
        if (map -> nodes[i].key == NULL){continue;}

        // Indent the output dependent on the depth (i.e. sub-maps will be
        // indented more than surface level values).
        for (int j = 0; j < indentation; ++j){printf("  ");}

        // Display the key value (string)
        printf("\"%s\": ", map->nodes[i].key);

        // If the value is a nested hashmap (recursive call)
        if (map->nodes[i].is_map)
        {
            // If nested hashmap, print recursively with increased indentation level
            printf("{\n");
            mpir_hashmap_display_internal(map->nodes[i].data.map, indentation + 1);

            // Print indentation for closing curly brace
            for (int j = 0; j < indentation; ++j){printf("  ");}

            printf("}\n");
        }

        // If the map is a value, display it (base-case).
        else if(!(map -> nodes[i].is_map))
        {
            printf("\"%s\"\n", map->nodes[i].data.value);
        }
    }
}

/// @brief Wrapper for mpir_hashmap_display_internal()
///
/// This function is a wrapper for the mpir_hashmap_display_internal() function, which recursively
/// displays a nested hashmaps key, value pairs to stdout. Use this function to print the hashmap,
/// as it sets the initial indentation level (unless you need to do this yourself?)
///
/// @param map Pointer to the hashmap structure to be displayed.
/// @note This function assumes that the hashmap has been properly initialized and contains valid data.
///
void mpir_hashmap_display(mpir_hashmap* map)
{
    mpir_hashmap_display_internal(map, 0);
}

int main()
{
    mpir_hashmap* map = mpir_hashmap_create();

    (void)mpir_hashmap_put_value(map, "key1", "value1");
    (void)mpir_hashmap_put_value(map, "key2", "value2");

    mpir_hashmap* nestedMap = mpir_hashmap_put_map(map, "nested_map");
    (void)mpir_hashmap_put_value(nestedMap, "nested_key", "nested_value");

    printf("Value for key1: %s\n", mpir_hashmap_get(map, "key1")); // Output: value1
    printf("Value for key2: %s\n", mpir_hashmap_get(map, "key2")); // Output: value2
    printf("Value for nested_map: %s\n", mpir_hashmap_get(map, "nested_map")); // Output: Nested mpir_hashmap (not printable)
    printf("Value for nested_key in nested_map: %s\n", mpir_hashmap_get(nestedMap, "nested_key")); // Output: nested_value

    (void)mpir_hashmap_display(map);
    (void)mpir_hashmap_free(map);
    return 0;
}
