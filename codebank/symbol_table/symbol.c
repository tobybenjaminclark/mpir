#include "mpir_symbol_context.h"
#include "mpir_symbol_variable.h"
#include "mpir_symbol_type.h"

/// @brief union structure for the 3 symbol types
typedef union
{
    mpir_symbol_variable *lexical_id;
    mpir_symbol_type *lexical_type;
    mpir_symbol_context *lexical_context;
} mpir_symbol_data;

/// @brief stores a symbol
typedef struct
{
    unsigned int numerical_symbol_id;
    mpir_symbol_data symbol
} mpir_symbol;

