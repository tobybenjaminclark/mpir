#include "mpir_warnings.h"

// Function to log messages based on log level
void mpir_warn(const char *format, ...)
{
    va_list args;
    va_start(args, format);
    printf(WARNING_PREFIX);
    vprintf(format, args);
    printf("\n");
    va_end(args);
}

// Function to log messages based on log level
void mpir_error(const char *format, ...)
{
    va_list args;
    va_start(args, format);
    fprintf(stderr, ERROR_PREFIX);
    vfprintf(stderr, format, args);
    fprintf(stderr, "\n");
    va_end(args);
}

// Function to log messages based on log level
void mpir_fatal(const char *format, ...)
{
    va_list args;
    va_start(args, format);
    fprintf(stderr, FATAL_PREFIX);
    vfprintf(stderr, format, args);
    fprintf(stderr, "\n");
    va_end(args);
}