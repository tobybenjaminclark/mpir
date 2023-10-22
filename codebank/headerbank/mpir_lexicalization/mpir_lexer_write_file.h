
// GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark
// This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
// License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.

#ifndef MPIR_COMPILER_MPIR_LEXER_WRITE_FILE_H
#define MPIR_COMPILER_MPIR_LEXER_WRITE_FILE_H

#include "../../headerbank/mpir_lexicalization/mpir_lexer.h"
#include "../../headerbank/mpir_misc/mpir_warnings.h"
#include "../../headerbank/mpir_token/mpir_token_write.h"

/// @brief Writes the tokens from an mpir_lexer to a file.
///
/// This function writes the tokens stored in the given mpir_lexer structure
/// to a file specified by the provided file path.
///
/// @param lexer A pointer to the mpir_lexer structure containing tokens to be written.
/// @param file_path The file path where the tokens will be written.
///
/// @return Returns 0 on success, and 1 on failure.
///
int mpir_lexer_write_file(mpir_lexer* lexer, const char* file_path);

#endif //MPIR_COMPILER_MPIR_LEXER_WRITE_FILE_H
