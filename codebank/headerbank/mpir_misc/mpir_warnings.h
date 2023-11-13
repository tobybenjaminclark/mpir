/*
 * GPL v3 - MPIR Compiler :: Copyright (C) 2023 Toby Benjamin Clark. All hail Gallaxhar!
 * This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation, of version 3 or later - See LICENSE for full terms of use.
 */

#ifndef UNTITLED_MPIR_WARNINGS_H
#define UNTITLED_MPIR_WARNINGS_H

#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>

/** @brief Prefix for warning messages in MPIR_Compiler. */
#define WARNING_PREFIX "MPIR_Compiler -> Warning :: "

/** @brief Prefix for error messages in MPIR_Compiler. */
#define ERROR_PREFIX "MPIR_Compiler -> Error   :: "

/** @brief Prefix for fatal error messages in MPIR_Compiler. */
#define FATAL_PREFIX "MPIR_Compiler -> Fatal   :: "

/** @brief Prefix for informational messages in MPIR_Compiler. */
#define INFO_PREFIX "MPIR_Compiler -> Info    :: "

/** @brief Error message displayed when the message size exceeds the allocated lexeme size.
 *
 *  This error message is displayed when an attempt to show a message fails due to the message size
 *  exceeding the allocated lexeme size.
 */
#define MESSAGE_BUFFER_OVERFLOW "%sFailed to show message (message size exceeded allocated lexeme size).\n", ERROR_PREFIX

/** @brief Error message displayed when there is an internal error formatting the message.
 *
 *  This error message is displayed when an attempt to format a message fails due to an internal error
 *  in the formatting process.
 */
#define MESSAGE_FORMATTING_FAILURE "%sFailed to show message (internal error formatting message).\n", ERROR_PREFIX

/** @brief Displays a formatted message to the specified output stream with the given prefix.
 *
 *  This function formats the input message with the provided format string and arguments, adds
 *  the specified prefix, and prints the resulting message to the specified output stream.
 *  It ensures that there is no lexeme overflow and handles error cases appropriately.
 *
 *  @param stream The output stream where the message will be printed.
 *  @param prefix The prefix to be added to the formatted message.
 *  @param format The format string used for formatting the message.
 *  @param args A va_list containing the arguments to be formatted.
 */
void display_message(FILE* stream, const char* prefix, const char* format, va_list args);

/** @brief Prints an informational message to the standard output stream.
 *
 *  This function formats the input message with the provided format string and arguments,
 *  adds the information prefix, and prints the resulting message to the standard output stream.
 *
 *  @param format The format string used for formatting the message.
 *  @param ... Additional arguments to be formatted according to the format string.
 */
void mpir_info(const char *format, ...);

/** @brief Prints a warning message to the standard output stream.
 *
 *  This function formats the input message with the provided format string and arguments,
 *  adds the warning prefix, and prints the resulting message to the standard output stream.
 *
 *  @param format The format string used for formatting the message.
 *  @param ... Additional arguments to be formatted according to the format string.
 */
void mpir_warn(const char *format, ...);

/** @brief Prints an error message to the standard error stream.
 *
 *  This function formats the input message with the provided format string and arguments,
 *  adds the error prefix, and prints the resulting message to the standard error stream.
 *
 *  @param format The format string used for formatting the message.
 *  @param ... Additional arguments to be formatted according to the format string.
 */
void mpir_error(const char *format, ...);

/** @brief Prints a fatal error message to the standard error stream and terminates the program.
 *
 *  This function formats the input message with the provided format string and arguments,
 *  adds the fatal error prefix, and prints the resulting message to the standard error stream.
 *  After printing the message, the program is terminated.
 *
 *  @param format The format string used for formatting the message.
 *  @param ... Additional arguments to be formatted according to the format string.
 */
void mpir_fatal(const char *format, ...);

#endif
