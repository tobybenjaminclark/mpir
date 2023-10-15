#include "../mpir_symbol_table/mpir_symbol_variable.h"

mpir_symbol_variable* initialize_variable_symbol(mpir_symbol_variable* variable_symbol, mpir_symbol_context* context, int _identifier)
{
    variable_symbol -> identifier = _identifier;
    variable_symbol -> lexical_context = context;
    return variable_symbol;
}

mpir_symbol_variable* create_variable_symbol(mpir_symbol_context* context, int identifier)
{
    // Allocate memory for the context symbol.
    mpir_symbol_variable* variable_symbol = (mpir_symbol_variable*)malloc(sizeof(mpir_symbol_variable));

    // Check memory-allocation was successful.
    if (variable_symbol == NULL)
    {
        mpir_fatal("No Remaining Free Memory (Failed to allocate memory for variable symbol).");
    }

    // Initialize context symbol
    else
    {
        variable_symbol = initialize_variable_symbol(variable_symbol, context, identifier);
    }

    return variable_symbol;
}

void free_variable_symbol(mpir_symbol_variable* variable_symbol)
{
    free(variable_symbol);
    return;
}


