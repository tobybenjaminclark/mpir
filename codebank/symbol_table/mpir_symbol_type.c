#include "mpir_symbol_type.h"

mpir_symbol_type* initialize_symbol_type(mpir_symbol_type* type_symbol, int _identifier)
{
    type_symbol -> identifier = _identifier;
    return type_symbol;
}

mpir_symbol_type* create_symbol_type(int identifier)
{
    // Allocate memory for the context symbol.
    mpir_symbol_type* type_symbol = (mpir_symbol_type*)malloc(sizeof(mpir_symbol_type));

    // Check memory-allocation was successful.
    if (type_symbol == NULL)
    {
        printf("failed to allocate memory for context symbol");
        exit(1);
    }

    // Initialize context symbol
    else
    {
        type_symbol = initialize_variable_symbol(type_symbol, identifier);
    }

    return type_symbol;
}

void free_symbol_type(mpir_symbol_type* type_symbol)
{
    free(type_symbol);
    return;
}
