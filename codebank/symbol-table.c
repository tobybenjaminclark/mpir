// stdio.h is the inbuilt library for input/output communications
// in the context of this code, it is used to print to the terminal.
#include <stdio.h>

// stdlib.h is the inbuilt standard library comprimising of a variety of functions.
// in the conext of this code, it is used to represent an EXIT_FAILURE message.
#include <stdlib.h>

// string.h is the inbuilt library for string manipulation
// in the context of this code, the strncpy function is used to copy a string
#include <string.h>

// symbol.c is a small library allowing for the creation of symbol structures (in the context of programming languages)
// in the context of this code, it is used to represent the elements of the symbol table, meaning a
// symbol table can be seen as a collection of symbols.
#include "symbol.c"

/// @brief Defining a type for a dynamically allocated symbol table.
typedef struct mpir_symbol_table
{
    mpir_symbol* symbols;
    int size;
    int capacity;
} mpir_symbol_table;

/// @brief Defining a function to create a dynamic symbol table
/// @param capacity Starting size of the symbol table that will be created.
mpir_symbol_table create_symbol_table(int capacity)
{
    mpir_symbol_table table;
    table.symbols = (mpir_symbol*)malloc(sizeof(mpir_symbol) * capacity);
    table.size = 0;
    table.capacity = capacity;
    return table;
}

/// @brief Defining a function to insert a symbol into the dynamic symbol table
/// @param table Structure of the current symbol table
/// @param new_symbol Symbol to be inserted (must be previously created)
///
/// When attempting to insert a symbol into a symbol table that is at full-capacity (there is no room left) the
/// following code will double the current capacity of the symbol table, before adding the new symbol. This is to
/// improve amortized performance of symbol table insertions, whilst still maintaining effective memory usage.
void insert_symbol(mpir_symbol_table* table, mpir_symbol* new_symbol)
{
    // Perform a check if there is room for the new symbol.
    if (table->size >= table->capacity)
    {
        // In the event there is no room, double the table capacity & reallocate memory.
        table->capacity = table->capacity * 2;
        table->symbols = (mpir_symbol*)realloc(table->symbols, sizeof(mpir_symbol) * table->capacity);

        // Check to ensure memory-reallocation was successful.
        if (table->symbols == NULL)
        {
            printf("Memory reallocation error.\n");
            exit(EXIT_FAILURE);
        }
    }
    
    // Insert the symbol into the symbol table.
    table->symbols[table->size++] = *new_symbol;
}

/// @brief Defining a function to output a symbol table to the console.
/// @param table Symbol table to be printed to console.
void print_symbol_table(const mpir_symbol_table* table)
{
    int i = 0;

    printf("Symbol Table:\nName\t\tType\n");
    for (i = 0; i < table->size; ++i)
    {
        printf("%s\t\t%s\n", table->symbols[i].identifier, table->symbols[i].type);
    }
}

/// @brief Frees a symbol table from memory.
/// @param table Symbol table to free from memory.
void free_symbol_table(mpir_symbol_table* table)
{
    // Free all symbols within
    free(table->symbols);

    // Set table size & capacity to zero.
    table->size = 0;
    table->capacity = 0;
}

int main()
{
    mpir_symbol_table symbol_table = create_symbol_table(100);

    mpir_symbol symbol_one = create_symbol("var 1", "int");
    insert_symbol(&symbol_table, &symbol_one);

    print_symbol_table(&symbol_table);
    free_symbol_table(&symbol_table);

    return 0;
}
