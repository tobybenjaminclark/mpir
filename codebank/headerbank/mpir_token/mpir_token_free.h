/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_TOKEN_FREE_H
#define MPIR_COMPILER_MPIR_TOKEN_FREE_H
#include "../../headerbank/mpir_token/mpir_token.h"

/**
 * @brief Frees the allocated memory for a token structure, releasing system resources.
 *
 * This function deallocates the memory occupied by a token structure previously created by the
 * mpir_create_token function. In the case of a NULL token being passed, it will do nothing, and
 * simply return.
 *
 * @param token A pointer to the token structure that needs to be deallocated.
 */
void mpir_free_token(mpir_token* token);

#endif //MPIR_COMPILER_MPIR_TOKEN_FREE_H
