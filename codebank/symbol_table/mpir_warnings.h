#include <stdio.h>
#include <stdarg.h>

#define WARNING_PREFIX "MPIR_Compiler -> Warning :: "
#define ERROR_PREFIX "MPIR_Compiler -> Error :: "
#define FATAL_PREFIX "MPIR_Comiler -> Fatal :: "

void mpir_warn(const char *format, ...);
void mpir_error(const char *format, ...);
void mpir_fatal(const char *format, ...);