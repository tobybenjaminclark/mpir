#include "mpir_symbol_context.h"

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
        printf("failed to allocate memory for context symbol");
        exit(1);
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