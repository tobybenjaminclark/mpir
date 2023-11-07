/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_protobuffer/mpir_protobuffer.h"

FILE* mpir_protobuffer_open_file(const char* file_path)
{
    FILE *input;        /* ← FILE pointer to store the protobuffer template file. */

    /*
     * Sets the current locale to the 'C' Locale, a.k.a. 'POSIX'/'classic'
     * POSIX is a superset of the default ASCII character set, allowing for special characters beyond this range, such
     * as special symbols (∀/∃), & emojis. This requires the use of wide character handling using the wchar_t datatype.
     */
    (void) setlocale(LC_ALL, "en_US.UTF-8");

    /* Attempt to open file, if fail, return an error! */
    if ((input = fopen(file_path, "r")) != NULL) return input;
    else
    {
        mpir_error(MPIR_PB_FNF, file_path);
        return NULL;
    }
}


int mpir_protobuffer_allocate_new_template(struct mpir_protobuffer_template*** templates, int* number_of_templates)
{
    /* Allocate memory for a new template */
    struct mpir_protobuffer_template* new_template = (struct mpir_protobuffer_template*)malloc(sizeof(struct mpir_protobuffer_template));

    if (new_template != NULL)
    {
        /* Initialize the new template's members, if necessary */
        new_template->template_name[0] = L'\0'; // Example initialization for the template name
        new_template->types[0] = NULL; // Example initialization for types array
        new_template->identifiers[0] = NULL; // Example initialization for identifiers array

        /* Reallocate memory for the templates array to accommodate the new template */
        *templates = (struct mpir_protobuffer_template**)realloc(*templates, (*number_of_templates + 1) * sizeof(struct mpir_protobuffer_template*));

        /* Add the new template to the array */
        (*templates)[*number_of_templates] = new_template;

        /* Increment the number of templates */
        ++(*number_of_templates);
        return 1;
    }
    else
    {
        mpir_fatal("mpir_protocolbuffer: failed to allocate memory for new template array");
        return 0;
    }
}

int mpir_parse_protobuffer_template(const wchar_t* file_path)
{
    struct mpir_protobuffer_template** templates;
    mpir_protobuffer_template_parser_state state = AWAITING_STRUCTURE;  /* ← Current state of the template parser. */
    FILE* file = mpir_protobuffer_open_file(file_path);                 /* ← File, opened using UTF-8 encoding     */
    bool parsing_complete = false;
    wchar_t current_char;
    wchar_t buffer[PB_BUFFER_SIZE];
    int buffer_index = 0;
    int number_of_templates = 0;

    /* Allocate memory for template */
    (void)malloc(number_of_templates * sizeof(struct mpir_protobuffer_template));

    while (!parsing_complete) {
        switch (state) {
            case AWAITING_STRUCTURE:
                if((current_char = fgetwc(file)) != L's')break;
                else if(current_char == WEOF) {mpir_fatal("mpir_protobuffer: couldnt parse file"); return 0;}
                else state = PARSING_STRUCTURE;
            case PARSING_STRUCTURE:
                if(fgetwc(file) == L't' && fgetwc(file) == L'r' && fgetwc(file) == L'u' && fgetwc(file) == L'c'
                && fgetwc(file) == L't' && fgetwc(file) == L'u' && fgetwc(file) == L'r' && fgetwc(file) == L'e')
                {
                    current_char = fgetwc(file);
                    while(current_char == L' ' || current_char == L'\t') current_char = fgetwc(file);
                    while(iswalpha(current_char))
                    {
                        wprintf(L"Current character is %lc , Buffer is '%ls' \n", current_char, buffer);
                        if(buffer_index >= PB_BUFFER_SIZE - 1)
                        {
                            mpir_fatal("mpir_protobuffer: exceeded buffer limit");
                            return 0;
                        }
                        else
                        {
                            buffer[buffer_index] = current_char;
                            (void)buffer_index++;
                            buffer[buffer_index] = L'\0';
                        }
                        current_char = fgetwc(file);
                    }

                    mpir_protobuffer_allocate_new_template(&templates, &number_of_templates);
                    // Check if memory allocation was successful before copying
                    if (templates[number_of_templates-1]->template_name != NULL) {
                        buffer_index = 0;
                        wprintf(L"type is %ls \n", buffer);
                        wcscpy(templates[number_of_templates-1]->template_name, buffer);
                        state = AWAITING_TYPE;
                        break;
                    } else {
                        mpir_fatal("mpir_protocolbuffer: failed to copy structure name into struct.");
                        return 0;
                    }
                }
                else
                {
                    mpir_fatal("mpir_protocbuffer : failed to parse 'structure'");
                    return 0;
                }
                break;
        case AWAITING_TYPE:
            current_char = fgetwc(file);
            while(current_char == L' ' || current_char == L'\t') current_char = fgetwc(file);
            if(iswalpha(current_char)) {state = PARSING_MEMBER_TYPE; break;}
            else{mpir_fatal("mpir_protocolbuffer: error parsing member type"); return 0;}

        case PARSING_MEMBER_TYPE:
            while(iswalpha(current_char))
            {
                wprintf(L"Current character is %lc , Buffer is '%ls' \n", current_char, buffer);
                if(buffer_index >= PB_BUFFER_SIZE - 1)
                {
                    mpir_fatal("mpir_protobuffer: exceeded buffer limit");
                    return 0;
                }
                else
                {
                    buffer[buffer_index] = current_char;
                    (void)buffer_index++;
                    buffer[buffer_index] = L'\0';
                }
                current_char = fgetwc(file);
            }

            // Check if memory allocation was successful before copying
            if (templates[number_of_templates]->types[number_of_templates-1] != NULL)
            {
                wprintf(L"type is %ls \n", buffer);
                wcscpy(templates[number_of_templates-1]->template_name, buffer);
                buffer_index = 0;
                state = AWAITING_TYPE;
                break;
            } else {
                mpir_fatal("mpir_protocolbuffer: failed to copy structure name into struct.");
                return 0;
            }
        case AWAITING_IDENTIFIER:
            break;
        case PARSING_MEMBER_IDENTIFIER:
            break;
        case DETECT_IF_END:
            break;
        default:
            mpir_error("mpir_protobuffer: parser in unexpected state");
            break;
    }; }
}

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

    mpir_parse_protobuffer_template("example.protobuf");

    return;
}