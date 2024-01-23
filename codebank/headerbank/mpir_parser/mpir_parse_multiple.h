/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef MPIR_COMPILER_MPIR_PARSE_MULTIPLE_H
#define MPIR_COMPILER_MPIR_PARSE_MULTIPLE_H

#define PARSE_MULTIPLE_STATEMENTS(type, parse_function, parser) \
    ({ \
        type** nodes = NULL; \
        int arg_index = 0; \
        type* arg; \
        \
        if (!psr) { \
            return NULL; \
        } \
        \
        while((arg = parse_function(parser)) != NULL) \
        { \
            type** temp = realloc(nodes, (arg_index + 2) * sizeof(type*)); \
            if (temp == NULL) \
            { \
                free(nodes); \
                return NULL; \
            } \
            nodes = temp; \
            \
            nodes[arg_index] = arg; \
            arg_index++; \
        } \
        if(arg_index == 0) return NULL; \
        \
        nodes[arg_index] = NULL; \
        nodes; \
    })

#endif
