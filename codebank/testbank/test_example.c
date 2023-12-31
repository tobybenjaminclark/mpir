/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include <stdlib.h>
#include "../testbank/mpir_test_tokenisation.h"

int main(int argc, char *argv[])
{
    if (argc < 2)
    {
        return 1;
    }

    int number = atoi(argv[1]);

    if(number == 1){return mpir_test_tokenisation();}

    return number;
}