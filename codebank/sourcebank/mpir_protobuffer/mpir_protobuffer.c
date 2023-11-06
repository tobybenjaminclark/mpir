/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_protobuffer/mpir_protobuffer.h"

void test() {
    /* Creating the mpir_token structure */
    CREATE_STRUCT(mpir_token, tok);

    /* Setting example identifier */
    mpir_token_type typ = IDENTIFIER;

    /* Initializing field */
    INIT_FIELD(tok, type, typ);

    /* Test Print */
    if (tok != NULL) {
        printf("type: %d\n", tok->type);
        free(tok);
    } else {
        printf("Failed to allocate memory for struct.\n");
    }

    return;
}