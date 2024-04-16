import argparse
import json
import os
from z3 import *


def parse_json_file(filename: str) -> dict|None:
    try:
        file = open(filename, 'r')
        data = json.load(file)
        file.close()
        return data
    except FileNotFoundError:
        print(f"File '{filename}' not found.")
        return None
    except json.JSONDecodeError as e:
        print(f"Error decoding AST in '{filename}': {e}")
        return None

def convert_function_call(fcall: dict) -> str:
    val = fcall["IDENTIFIER"] + "("
    for index, arg in enumerate(fcall["ARGUMENTS"]):
        val = val + convert_expression(arg["VALUE"]) + (", " if index < len(fcall["ARGUMENTS"]) - 1 else "")
    val = val + ")"
    return val


def convert_expression_type(expr) -> str:
    if expr["DATATYPE"] == "OPERATOR": return str(convert_expression_type(expr["LEFT"])) + " " + " " + expr["DATA"] + str(convert_expression_type(expr["RIGHT"]))
    return expr["DATA"]

def convert_expression(expr: dict) -> str:
    if "TYPE" not in expr: return convert_expression_type(expr)
    match(expr["TYPE"]):
        case "FUNCTION_CALL":
            return convert_function_call(expr)
        case "EXPRESSION_IDENTIFIER":
            return expr["IDENTIFIER"]
        case "EXPRESSION_NUMERICAL_LITERAL":
            try:
                return str(expr["VALUE"])
            except:
                print(expr)

        case "EXPRESSION_OPERATOR":
            return convert_expression(expr["LEFT"]) + " " + expr["IDENTIFIER"] + " " + convert_expression(expr["RIGHT"])
        case "EXPRESSION_STRING_LITERAL":
            return expr["IDENTIFIER"]
        case "FUNCTION_CALL":
            return "func"


    if(expr["TYPE"] == ""):
        pass


def convert_do_statement(statement) -> str:

    lines = ""
    for on_statement in statement["ON_STATEMENTS"]:
        lines = lines + ("if (" + convert_expression(statement["EXPRESSION"]) + ") ==  " + str(on_statement["MATCH_VALUE"]) + ": ")
        lines = lines + str(on_statement["MATCH_COMMANDS"][0]["IDENTIFIER"]) + " = " + convert_expression(on_statement["MATCH_COMMANDS"][0]["EXPRESSION"]) + "\n\t"
    return lines


def show_statement(statement, output_file):
    if statement["TYPE"] == "TYPE_ASSIGNMENT":
        output_file.write(statement["IDENTIFIER"] + ": " + statement["ASSIGNED_TYPE"] + "\n")
    elif statement["TYPE"] == "VALUE_ASSIGNMENT":
        output_file.write(statement["IDENTIFIER"] + " = " + convert_expression(statement["EXPRESSION"]) + "\n")
    elif statement["TYPE"] == "FUNCTION_CALL":
        output_file.write(convert_function_call(statement) + "\n")
    elif statement["TYPE"] == "TRYCAST_STATEMENT":
        output_file.write("TRYCAST!\n")
    elif statement["TYPE"] == "DO_STATEMENT":
        output_file.write(convert_do_statement(statement) + "\n")
    elif statement["TYPE"] == "IF_STATEMENT":
        output_file.write("if (" + convert_expression(statement["EXPRESSION"]) + "):\n")
        for statement2 in statement["MATCH_COMMANDS"]:
            output_file.write("\t\t")
            show_statement(statement2, output_file)

        

def build_python(ast: dict[str, any], output_file_path: str):
    print("Building python to ", output_file_path)
    try:
        if "CONTENTS" not in ast:
            print("CONTENTS NOT IN AST!")
            exit(1)

        with open(output_file_path, 'w') as output_file:
            output_file.write("# Generated using the MPIR Compiler.\n\n")

            # build types
            for node in filter(lambda v: v["TYPE"] == "TYPE_DECLARATION", ast["CONTENTS"]):
                identifier = node["IDENTIFIER"]
                output_file.write(f"{identifier} = type('{identifier}', (), {{}})\n\n")
            output_file.write("Numerical = type('Numerical', (float, ), {})\n\n")

            # build functions
            for node in filter(lambda v: v["TYPE"] == "FUNCTION_DECLARATION", ast["CONTENTS"]):
                output_file.write("def " + node["IDENTIFIER"] + "(")
                for index, arg in enumerate(node["ARGUMENTS"]):
                    output_file.write(arg + ": " + node["INPUTS"][index]["TYPE"] + (", " if index < len(node["ARGUMENTS"]) - 1 else ""))
                output_file.write(") -> " + node["RETURN_TYPE"] + ":\n")
                for statement in node["BODY"]:
                    output_file.write("\t")
                    show_statement(statement, output_file)
                output_file.write("\n\n")

    except Exception as e:
        with open(output_file_path, 'w') as output_file:
            output_file.write("# " + str(e))
