#include <stdio.h>
#include <stdlib.h>

typedef struct
{
    char* identifier;
} mpir_symbol_variable;

mpir_symbol_variable* initialize_variable_symbol(mpir_symbol_variable* variable_symbol, int _identifier);
mpir_symbol_variable* create_variable_symbol(int identifier);
void free_variable_symbol(mpir_symbol_variable* context_symbol);