#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "symbol.c"

/// @brief Defining a type for a dynamically allocated symbol table.
typedef struct symbol_table
{
    symbol* symbols;
    int size;
    int capacity;
} symbol_table;

/// @brief Defining a function to create a dynamic symbol table
/// @param capacity Starting size of the symbol table that will be created.
symbol_table create_symbol_table(int capacity)
{
    symbol_table table;
    table.symbols = (symbol*)malloc(sizeof(symbol) * capacity);
    table.size = 0;
    table.capacity = capacity;
    return table;
}

/// @brief Defining a function to insert a symbol into the dynamic symbol table
/// @param table Structure of the current symbol table
/// @param new_symbol Symbol to be inserted (must be previously created)
void insert_symbol(symbol_table* table, symbol* new_symbol)
{
    if (table->size >= table->capacity)
    {
        // Double the capacity if the symbol table is full
        table->capacity *= 2;
        table->symbols = (symbol*)realloc(table->symbols, sizeof(symbol) * table->capacity);
        if (table->symbols == NULL)
        {
            printf("Memory reallocation error.\n");
            exit(EXIT_FAILURE);
        }
    }
    
    table->symbols[table->size++] = *new_symbol;
}

/// @brief Defining a function to output a symbol table to the console.
/// @param table Symbol table to be printed to console.
void print_symbol_table(const symbol_table* table)
{
    printf("Symbol Table:\n");
    printf("Name\t\tType\n");
    for (int i = 0; i < table->size; ++i)
    {
        printf("%s\t\t%s\n", table->symbols[i].identifier, table->symbols[i].type);
    }
}

/// @brief Frees a symbol table from memory.
/// @param table Symbol table to free from memory.
void free_symbol_table(symbol_table* table)
{
    free(table->symbols);
    table->size = 0;
    table->capacity = 0;
}

int main()
{
    symbol_table symbol_table = create_symbol_table(100);

    symbol symbol_one = create_symbol("var 1", "int");
    insert_symbol(&symbol_table, &symbol_one);

    print_symbol_table(&symbol_table);
    free_symbol_table(&symbol_table);

    return 0;
}
