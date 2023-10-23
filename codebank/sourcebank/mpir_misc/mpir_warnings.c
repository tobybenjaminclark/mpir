/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#include "../../headerbank/mpir_misc/mpir_warnings.h"

/** @brief Displays a formatted message to the specified output stream with the given prefix.
 *
 * This function formats the input message with the provided format string and arguments, adds
 * the specified prefix, and prints the resulting message to the specified output stream.
 * It ensures that there is no buffer overflow and handles error cases appropriately.
 *
 * @param stream The output stream where the message will be printed.
 * @param prefix The prefix to be added to the formatted message.
 * @param format The format string used for formatting the message.
 * @param args A va_list containing the arguments to be formatted.
 */
void display_message(FILE* stream, const char* prefix, const char* format, va_list args)
{
    /* Declaring a buffer to store the displayed message within. After this, the message is
     * formatted within the buffer, and checked to ensure no buffer overflow.
     */
    char buffer[4096];
    if (sprintf(buffer, format, args) >= 0)
    {
        /* Print the formatted message to the output stream with the specified prefix
         * Check if fprintf was successful, if not, print an error message to stderr
         */
        if (fprintf(stream, "%s%s\n", prefix, buffer) < 0)
        {
            /* Display an error message indicating a buffer overflow. */
            fprintf(stderr, MESSAGE_BUFFER_OVERFLOW);
        }
    }
    else
    {
        /* Display an error message indicating a message formatting failure. */
        fprintf(stderr, MESSAGE_FORMATTING_FAILURE);
    }
}

/** @brief Prints an informational message to the standard output stream.
 *
 * This function formats the input message with the provided format string and arguments,
 * adds the information prefix, and prints the resulting message to the standard output stream.
 *
 * @param format The format string used for formatting the message.
 * @param ... Additional arguments to be formatted according to the format string.
 */
void mpir_info(const char *format, ...)
{
    /* va_list is an argument list of variable length, allowing for string formatting. It
     * is initialized with the last named parameter (format)
     */
    va_list args;
    va_start(args, format);

    /* Call the display_message function to format with the information prefix, and output
     * to the stdout stream.
     */
    display_message(stdout, INFO_PREFIX, format, args);
    va_end(args);
}

/** @brief Prints a warning message to the standard output stream.
 *
 * This function formats the input message with the provided format string and arguments,
 * adds the warning prefix, and prints the resulting message to the standard output stream.
 *
 * @param format The format string used for formatting the message.
 * @param ... Additional arguments to be formatted according to the format string.
 */
void mpir_warn(const char *format, ...)
{
    /* va_list is an argument list of variable length, allowing for string formatting. It
     * is initialized with the last named parameter (format)
     */
    va_list args;
    va_start(args, format);

    /* Call the display_message function to format with the warning prefix, and output
     * to the stdout stream.
     */
    display_message(stdout, WARNING_PREFIX, format, args);
    va_end(args);
}

/** @brief Prints an error message to the standard error stream.
 *
 * This function formats the input message with the provided format string and arguments,
 * adds the error prefix, and prints the resulting message to the standard error stream.
 *
 * @param format The format string used for formatting the message.
 * @param ... Additional arguments to be formatted according to the format string.
 */
void mpir_error(const char *format, ...)
{
    /* va_list is an argument list of variable length, allowing for string formatting. It
     * is initialized with the last named parameter (format)
     */
    va_list args;
    va_start(args, format);

    /* Call the display_message function to format with the error prefix, and output
     * to the stderr stream, indicating it is an erroneous message.
     */
    display_message(stderr, ERROR_PREFIX, format, args);
    va_end(args);
}

/** @brief Prints a fatal error message to the standard error stream and terminates the program.
 *
 * This function formats the input message with the provided format string and arguments,
 * adds the fatal error prefix, and prints the resulting message to the standard error stream.
 * After printing the message, the program is terminated.
 *
 * @param format The format string used for formatting the message.
 * @param ... Additional arguments to be formatted according to the format string.
 */
void mpir_fatal(const char *format, ...)
{
    /* va_list is an argument list of variable length, allowing for string formatting. It
     * is initialized with the last named parameter (format)
     */
    va_list args;
    va_start(args, format);

    /* Call the display_message function to format with the information prefix, and output
     * to the stderr stream, indicating it is an erroneous message.
     */
    display_message(stderr, FATAL_PREFIX, format, args);
    va_end(args);
}
