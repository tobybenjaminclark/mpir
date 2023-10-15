#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#define INITIAL_CAPACITY 16

// Enum to store entry type: Context or Symbol
typedef enum 
{
    mpir_context,
    mpir_symbol
} mpir_entry_type;

// Enum to store 
typedef union
{
    int value;
    mpir_symbol_context* map;
} mpir_symbol_table_value;

typedef struct
{
    char* key;
    mpir_entry_type entry_type;
    mpir_symbol_table_value entry_value;
} mpir_symbol_table_entry;

typedef struct
{
    mpir_symbol_table_entry* table;
    size_t size;
    size_t capacity;
} mpir_symbol_context;