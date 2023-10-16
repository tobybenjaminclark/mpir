#include "../../includebank/mpir_symbol_table/mpir_symbol_context.h"
#include "../../includebank/mpir_symbol_table/mpir_symbol_variable.h"
#include "../../includebank/mpir_symbol_table/mpir_symbol_type.h"

/// @brief stores the symbol types
typedef enum
{
  symbol_variable,
  symbol_type,
  symbol_context
} mpir_symbol_type;

/// @brief union structure for the 3 symbol types
typedef union
{
    mpir_symbol_variable *lexical_id;
    mpir_symbol_type *lexical_type;
    mpir_symbol_context *lexical_context;
} mpir_internal_symbol;

/// @brief stores a symbol
typedef struct
{
    // Generic Symbol Data 
    unsigned int numerical_symbol_id;
    unsigned int line_declared;
    char* lexical_identifier;

    // stores the lexical context of the variable, i.e. is it global of local to function, if so what?  
    mpir_symbol_context lexical_context;

    // stores info about the variable
    char* symbol_documentation;

    // stores type-specific data in a sub-struct (see union)
    mpir_symbol_type symbol_type;
    mpir_internal_symbol* symbol;
    
} mpir_symbol;