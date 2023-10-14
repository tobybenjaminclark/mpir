#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Structure to represent a symbol
typedef struct symbol
{
    char name[50];
    char type[50];
    // Add more fields as needed, e.g., memory location, value, etc.
} symbol;

// Structure to represent a symbol table
typedef struct symbol_table {
    symbol* symbols;
    int size;
    int capacity;
} symbol_table;

// Function to initialize a symbol table
void initialize_symbol_table(symbol_table* table, int capacity)
{
    table->symbols = (symbol*)malloc(sizeof(symbol) * capacity);
    table->size = 0;
    table->capacity = capacity;
}

// Function to insert a symbol into the symbol table
void insert_symbol(symbol_table* table, const char* name, const char* type)
{
    if (table->size < table->capacity) {
        symbol symbol;
        strncpy(symbol.name, name, sizeof(symbol.name) - 1);
        strncpy(symbol.type, type, sizeof(symbol.type) - 1);
        table->symbols[table->size++] = symbol;
    } else {
        printf("Symbol table is full. Cannot insert more symbols.\n");
    }
}

// Function to print the symbols in the symbol table
void print_symbol_table(const symbol_table* table)
{
    printf("Symbol Table:\n");
    printf("Name\t\tType\n");
    for (int i = 0; i < table->size; ++i) {
        printf("%s\t\t%s\n", table->symbols[i].name, table->symbols[i].type);
    }
}

// Function to free memory allocated for the symbol table
void free_symbol_table(symbol_table* table)
{
    free(table->symbols);
    table->size = 0;
    table->capacity = 0;
}

int main()
{
    // Create a symbol table with a capacity of 100
    symbol_table symbolTable;
    initialize_symbol_table(&symbolTable, 100);

    // Insert symbols into the symbol table
    insert_symbol(&symbolTable, "variable1", "int");
    insert_symbol(&symbolTable, "variable2", "float");
    insert_symbol(&symbolTable, "function1", "void");

    // Print the symbol table
    print_symbol_table(&symbolTable);

    // Free memory allocated for the symbol table
    free_symbol_table(&symbolTable);

    return 0;
}
