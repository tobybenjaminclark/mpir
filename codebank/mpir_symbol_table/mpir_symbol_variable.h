#include <stdio.h>
#include <stdlib.h>
#include "../mpir_logging/mpir_warnings.h"
#include "../mpir_symbol_table/mpir_symbol_context.h"

typedef struct
{
    char* identifier;
    mpir_symbol_context* lexical_context;

} mpir_symbol_variable;

mpir_symbol_variable* initialize_variable_symbol(mpir_symbol_variable* variable_symbol, mpir_symbol_context* context, int _identifier);
mpir_symbol_variable* create_variable_symbol(mpir_symbol_context* context, int identifier);
void free_variable_symbol(mpir_symbol_variable* context_symbol);