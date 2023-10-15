#include "mpir_symbol_variable.h"

mpir_symbol_variable* initialize_variable_symbol(mpir_symbol_variable* variable_symbol, int _identifier)
{
    variable_symbol -> identifier = _identifier;
    return variable_symbol;
}

mpir_symbol_variable* create_variable_symbol(int identifier)
{
    // Allocate memory for the context symbol.
    mpir_symbol_variable* variable_symbol = (mpir_symbol_variable*)malloc(sizeof(mpir_symbol_variable));

    // Check memory-allocation was successful.
    if (variable_symbol == NULL)
    {
        printf("failed to allocate memory for context symbol");
        exit(1);
    }

    // Initialize context symbol
    else
    {
        variable_symbol = initialize_variable_symbol(variable_symbol, identifier);
    }

    return variable_symbol;
}

void free_variable_symbol(mpir_symbol_variable* variable_symbol)
{
    free(variable_symbol);
    return;
}


