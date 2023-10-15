#include "../mpir_symbol_table/mpir_symbol_table.h"



mpir_symbol_context* mpir_context_create()
{
    mpir_symbol_context* map = malloc(sizeof(mpir_symbol_context));
    map -> size = 0;
    map -> capacity = INITIAL_CAPACITY;
    map -> table = malloc(INITIAL_CAPACITY * sizeof(mpir_symbol_table_entry));
    return map;
}

bool mpir_context_resize(mpir_symbol_context* map)
{
    return true;
}

bool mpir_context_insert(mpir_symbol_context* map, char* key, char* value)
{
    // Check capacity
    if (map -> size >= map -> capacity / 2)
    {
        if(!mpir_context_resize(map))
        {
            return false;
        }
    }

    return true;
}