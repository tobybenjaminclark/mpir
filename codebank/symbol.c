
/// @brief Defining a type for a singular symbol, and it's associated data.
typedef struct symbol
{
    char identifier[50];
    char type[50];
} symbol;

symbol create_symbol(const char* identifier, const char* type)
{
    symbol created_symbol;
    strncpy(created_symbol.identifier, identifier, sizeof(created_symbol.identifier) - 1);
    strncpy(created_symbol.type, type, sizeof(created_symbol.type) - 1);
    return created_symbol;
}