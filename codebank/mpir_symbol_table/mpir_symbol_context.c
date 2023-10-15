#include "../mpir_symbol_table/mpir_symbol_context.h"

mpir_symbol_context* initialize_context_symbol(mpir_symbol_context* context_symbol, int _identifier)
{
    context_symbol -> identifier = _identifier;
    return context_symbol;
}

mpir_symbol_context* create_context_symbol(int identifier)
{
    // Allocate memory for the context symbol.
    mpir_symbol_context* context_symbol = (mpir_symbol_context*)malloc(sizeof(mpir_symbol_context));

    // Check memory-allocation was successful.
    if (context_symbol == NULL)
    {
        mpir_fatal("No Remaining Free Memory (Failed to allocate memory for context symbol).");
    }

    // Initialize context symbol
    else
    {
        context_symbol = initialize_context_symbol(context_symbol, identifier);
    }

    return context_symbol;
}

void free_context_symbol(mpir_symbol_context* context_symbol)
{
    free(context_symbol);
    return;
}