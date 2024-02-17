/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_token/mpir_token_write.h"

/**
 * @brief Stores the mapping between the token ID's and names.
 *
 * See mpir_token.h for more information regarding the implementation and actual names of this. It can be used similarly
 * to a dictionary/hash-map to retrieve the values.
 */
const char* token_names[] = { TOKEN_NAME_MAP };

/**
 * @brief Writes an MPIR token to a specified file.
 *
 * This expression writes the given MPIR token to the provided file stream in a specific format.
 * The token type, lexeme, line index, and column index are written to the file in the following order:
 * - Token type (e.g., NUMERICAL_LITERAL, STRING_LITERAL, OPERATOR, IDENTIFIER, KEYWORD)
 * - Token lexeme (string representation of the token)
 * - Token line index (line number in the source file where the token is located)
 * - Token column index (column number in the source file where the token starts)
 *
 * The file must be opened in an appropriate mode before calling this expression. It is the caller's responsibility to
 * manage file opening and closing. The expression also performs basic error checking, ensuring that the file is already
 * open before writing the token data. Token end and start points are symbolized by START_TOK & END_TOK
 *
 * @param token A pointer to the MPIR token structure containing information about the token to be written.
 * @param file A pointer to the FILE structure representing the file where the token data will be written.
 * @return Returns 0 upon successful writing of the token. If the file is not open (file == NULL), an error message is printed, and the expression returns 1.
 */
int mpir_write_token(mpir_token* token, FILE* file, short int indentation, short int add_comma)
{
    /* The file must already be open. */
    if(file == NULL)
    {
        fprintf(stderr, "Error: Unable to write token to file.\n");
        return 1;
    }

    /* Write data to the file in JSON-like format with specified indentation */
    /*fprintf(file, "%*s{\n", (indentation*4), "");
    fprintf(file, "%*s\"type\": %s,\n", (indentation*4) + 4, "", token_names[token->type]); */
    if(token->type == NEWLINE)
    {
        fprintf(file, "\\n\n");
        return 0;
    }
    if(token->type == IDENTIFIER)
    {
        fwprintf(file, L"%ls ", token->lexeme);
        return 0;
    }
    fprintf(file, "%s ", token_names[token->type]);

    /*fwprintf(file, L"%*s\"lexeme\": \"%ls\",\n", (indentation*4) + 4, "", token->lexeme);
    //fprintf(file, "%*s\"line_index\": %lu,\n", (indentation*4) + 4, "", token->line_index);
    //fprintf(file, "%*s\"column_index\": %lu\n", (indentation*4) + 4, "", token->column_index);
    //fprintf(file, "%*s}%s\n", (indentation*4), "", (add_comma) ? "," : ""); */

    return 0;
}



int mpir_write_token_md(mpir_token* token, FILE* file)
{

    /* The file must already be open. */
    if(file == NULL)
    {
        fprintf(stderr, "Error: Unable to write token to file.\n");
        return 1;
    }

    /* Write data to the file in JSON-like format with specified indentation */
    if((token->type) == NEWLINE)
    {
        fprintf(file, "<code><b>\\n</b></code><br>\n");
        return 0;
    }
    else if((token->type) == IDENTIFIER)
    {
        fwprintf(file, L"<code>'%ls'</code> ", token->lexeme);
        return 0;
    }
    else if((token->type) == indentation)
    {
        fprintf(file, "<code><u>&nbsp;&nbsp;&nbsp;&nbsp;</u></code>");
        return 0;
    }
    else fprintf(file, "<code>%s</code> ", token_names[token->type]);

    return 0;
}