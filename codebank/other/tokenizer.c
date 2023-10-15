#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <ctype.h>

// Grammar Definition
// statement            ::=   string_definition | string_expression
// string_definition    ::=   'string' variable_name string_literal
// string_expression    ::=   string_expression '+' string | string
// string               ::=   char | string char

void tokenize_string();
void tokenize_variable_name();
void tokenize_string_literal();
void tokenize_string_expression();
void tokenize_string_definition();
void tokenize_statement();
void tokenize_consume_character(char expected);

// global declaration
char* input;

void tokenize_consume_character(char expected)
{
	if (*input == expected)
	{
		input++;
	}
	else
	{
		printf("error: Unexpected character %c \n", *input);
		exit(1);
	}
}

void tokenize_string()
{
	printf("tokenize_string: %s \n", input);
	int alpha_contender = isalpha(*input);
    while (alpha_contender)
	{
		printf("tokenize_string: %c \t:\t %d \n", *input, alpha_contender);
        input++;
		alpha_contender = isalpha(*input);
    }
}

int main()
{
    // Taking Input
    char line_one[50];
    printf("Type line 1\n");
    fgets(line_one, sizeof(line_one), stdin);

    line_one[strcspn(line_one, "\n")] = '\0'; // Remove newline character

    input = line_one;  // Assign the input pointer to line_one

    printf("input is '%s'\n", input);
    printf("first character is '%c' \n", *input);

    tokenize_statement();

    return 0;
}

void tokenize_variable_name()
{
	printf("tokenize_variable_name: %s \n", input);
	tokenize_string();
}

void tokenize_string_literal()
{
	printf("tokenize_string_literal: %s \n", input);
	tokenize_consume_character('"');
	tokenize_string();
	tokenize_consume_character('"');
}

// string_expression    ::=   string_expression '+' string | string
void tokenize_string_expression()
{
	printf("tokenize_string_expression: %s \n", input);
	tokenize_string();
	while(*input == '+')
	{
		tokenize_consume_character('+');
		tokenize_string();
	}
}

void tokenize_string_definition()
{
	printf("tokenize_string_definition: %s \n", input);
	tokenize_consume_character('s');
	tokenize_consume_character('t');
	tokenize_consume_character('r');
	tokenize_consume_character('i');
	tokenize_consume_character('n');
	tokenize_consume_character('g');
	tokenize_consume_character(' ');
	tokenize_variable_name();
	tokenize_consume_character(' ');
	tokenize_string_literal();
}

void tokenize_statement()
{
	printf("tokenize_statement: %s \n", input);
	if (*input == 's')
	{
		tokenize_string_definition();
	}
	else
	{
		tokenize_string_expression();
	}
}