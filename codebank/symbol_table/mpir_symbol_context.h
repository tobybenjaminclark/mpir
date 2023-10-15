#include <stdio.h>
#include <stdlib.h>

/// @brief structure to store context (function) information
typedef struct
{
    char* identifier
} mpir_symbol_context;

mpir_symbol_context* initialize_context_symbol(mpir_symbol_context* context_symbol, int _identifier);
mpir_symbol_context* create_context_symbol(int identifier);
void free_context_symbol(mpir_symbol_context* context_symbol);