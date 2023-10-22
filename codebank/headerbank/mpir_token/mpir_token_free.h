#ifndef MPIR_COMPILER_MPIR_TOKEN_FREE_H
#define MPIR_COMPILER_MPIR_TOKEN_FREE_H
#include "../../headerbank/mpir_token/mpir_token.h"

/// @brief Frees the allocated memory for a token structure, releasing system resources.
///
/// This function deallocates the memory occupied by a token structure previously created by the
/// mpir_create_token function. In the case of a NULL token being passed, it will do nothing, and
/// simply return.
///
/// @param token A pointer to the token structure that needs to be deallocated.
///
void mpir_free_token(mpir_token* token);

#endif //MPIR_COMPILER_MPIR_TOKEN_FREE_H
