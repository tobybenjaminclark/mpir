#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define INITIAL_SIZE 10
#define LOAD_FACTOR_THRESHOLD 0.7

// Node structure for linked list
struct mpir_node
{
    char* key;
    char* value;
    struct mpir_node* next;
};

// Hash map structure
struct mpir_hash_map 
{
    struct mpir_node** buckets;
    int size;
    int count;
};

// Hash function
int hash(struct mpir_hash_map* map, char* key)
{
    int i = 0;
    int hash = 0;
    for (i = 0; key[i] != '\0'; i++)
    {
        hash = (hash + key[i]) % map->size;
    }
    return hash;
}

// Initialize a new node
struct mpir_node* create_node(char* key, char* value)
{
    struct mpir_node* newNode = (struct mpir_node*)malloc(sizeof(struct mpir_node));
    newNode->key = strdup(key);
    newNode->value = strdup(value);
    newNode->next = NULL;
    return newNode;
}

// Initialize a new hash map
struct mpir_hash_map* create_hash_map() {
    struct mpir_hash_map* map = (struct mpir_hash_map*)malloc(sizeof(struct mpir_hash_map));
    map->size = INITIAL_SIZE;
    map->count = 0;
    map->buckets = (struct mpir_node**)calloc(map->size, sizeof(struct mpir_node*));
    return map;
}

// Resize the hash map
void resize_hash_map(struct mpir_hash_map* map) {
    int newSize = map->size * 2;
    struct mpir_node** newBuckets = (struct mpir_node**)calloc(newSize, sizeof(struct mpir_node*));

    // Rehash all keys into the new buckets
    for (int i = 0; i < map->size; i++) {
        struct mpir_node* current = map->buckets[i];
        while (current != NULL) {
            struct mpir_node* next = current->next;
            int index = hash(map, current->key);
            current->next = newBuckets[index];
            newBuckets[index] = current;
            current = next;
        }
    }

    free(map->buckets);
    map->buckets = newBuckets;
    map->size = newSize;
}

// Insert key-value pair into hash map
void hash_map_insert(struct mpir_hash_map* map, char* key, char* value) {
    int index = hash(map, key);
    struct mpir_node* newNode = create_node(key, value);
    newNode->next = map->buckets[index];
    map->buckets[index] = newNode;
    map->count++;

    // Check load factor and resize if necessary
    double loadFactor = (double)map->count / map->size;
    if (loadFactor > LOAD_FACTOR_THRESHOLD) {
        resize_hash_map(map);
    }
}

// Get value associated with a key from hash map
char* hash_map_retrieve(struct mpir_hash_map* map, char* key) {
    int index = hash(map, key);
    struct mpir_node* current = map->buckets[index];
    while (current != NULL) {
        if (strcmp(current->key, key) == 0) {
            return current->value;
        }
        current = current->next;
    }
    return NULL;
}

// Free memory used by the hash map
void free_node(struct mpir_node* node) {
    if (node == NULL) {
        return;
    }
    free_node(node->next);
    free(node->key);
    free(node->value);
    free(node);
}

void free_hash_map(struct mpir_hash_map* map) {
    for (int i = 0; i < map->size; i++) {
        free_node(map->buckets[i]);
    }
    free(map->buckets);
    free(map);
}

int main() {
    // Create a new hash map
    struct mpir_hash_map* map = create_hash_map();

    // Insert key-value pairs into the hash map
    hash_map_insert(map, "name", "John");
    hash_map_insert(map, "age", "30");
    hash_map_insert(map, "city", "New York");

    // Retrieve and print values from the hash map
    printf("Name: %s\n", hash_map_retrieve(map, "name"));
    printf("Age: %s\n", hash_map_retrieve(map, "age"));
    printf("City: %s\n", hash_map_retrieve(map, "city"));

    // Free memory used by the hash map
    free_hash_map(map);

    return 0;
}
