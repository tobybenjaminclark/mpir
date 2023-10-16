#include <stdio.h>
#include <stdlib.h>
#include "../../includebank/mpir_logging/mpir_warnings.h"

/// @brief structure to store type information
typedef struct
{
    char* identifier;
} mpir_symbol_type;

mpir_symbol_type* initialize_symbol_type(mpir_symbol_type* type_symbol, int _identifier);
mpir_symbol_type* create_symbol_type(int identifier);
void free_symbol_type(mpir_symbol_type* type_symbol);