
/// @brief Defining a type for a singular symbol, and it's associated data.
typedef struct mpir_symbol
{
    char identifier[50];
    char type[50];
} mpir_symbol;

/// @brief Defining a Constructor Function for the Symbol Type
/// @param identifier Symbol Identifier (the name of the variable)
/// @param type Symbol Type (the type of the variable)
/// @return Created symbol structure.
mpir_symbol create_symbol(const char* identifier, const char* type)
{
    mpir_symbol created_symbol;
    strncpy(created_symbol.identifier, identifier, sizeof(created_symbol.identifier) - 1);
    strncpy(created_symbol.type, type, sizeof(created_symbol.type) - 1);
    return created_symbol;
}