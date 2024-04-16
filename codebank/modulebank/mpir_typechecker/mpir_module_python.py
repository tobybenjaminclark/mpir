import argparse
import json
import os
from z3 import *
from typing_context import *

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
    for index, on_statement in enumerate(statement["ON_STATEMENTS"]):
        lines = lines + ("if (" + convert_expression(statement["EXPRESSION"]) + ") ==  " + str(on_statement["MATCH_VALUE"]) + ": ")
        lines = lines + str(on_statement["MATCH_COMMANDS"][0]["IDENTIFIER"]) + " = " + convert_expression(on_statement["MATCH_COMMANDS"][0]["EXPRESSION"]) + "\n\t"
        if index != len(statement["ON_STATEMENTS"]) - 1: lines += "el"
            
    return lines


def z3_to_string(expr):
    if is_and(expr):
        return "(" + z3_to_string(expr.children()[0]) + " and " + z3_to_string(expr.children()[1]) + ")"
    elif is_or(expr):
        return "(" + z3_to_string(expr.children()[0]) + " or " + z3_to_string(expr.children()[1]) + ")"
    elif is_not(expr):
        return "not " + z3_to_string(expr.children()[0])
    else:
        return str(expr)
    
def convert_trycast_statement(statement, context) -> str:
    set_option('smtlib2_compliant', True)
    set_option('pretty_print', True)

    lines = ""
    c_typ = get_type_from_context(context, statement["CASTED_IDENTIFIER"])
    cond = (str(z3_to_string(c_typ.logic.constraint()))).replace("σ", statement["DOMINANT_IDENTIFIER"])
    for index, on_statement in enumerate(statement["ON_STATEMENTS"]):
        lines += "if(" + cond + ") == " + ("True" if on_statement["MATCH_VALUE"] == 1 else "False") + ": " + convert_expression(on_statement["MATCH_COMMANDS"][0]["EXPRESSION"]) + "\n\t"
        if index != len(statement["ON_STATEMENTS"]) - 1: lines += "el"
    return lines

def show_statement(statement, output_file, context):
    if statement["TYPE"] == "TYPE_ASSIGNMENT":
        output_file.write(statement["IDENTIFIER"] + ": " + statement["ASSIGNED_TYPE"] + "\n")
    elif statement["TYPE"] == "VALUE_ASSIGNMENT":
        output_file.write(statement["IDENTIFIER"] + " = " + convert_expression(statement["EXPRESSION"]) + "\n")
    elif statement["TYPE"] == "FUNCTION_CALL":
        output_file.write(convert_function_call(statement) + "\n")
    elif statement["TYPE"] == "TRYCAST_STATEMENT":
        output_file.write(convert_trycast_statement(statement, context) + "\n")
    elif statement["TYPE"] == "DO_STATEMENT":
        output_file.write(convert_do_statement(statement) + "\n")

        

def build_python(ast: dict[str, any], output_file_path: str, context):
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
                    show_statement(statement, output_file, context)
                output_file.write("\n\n")

    except Exception as e:
        with open(output_file_path, 'w') as output_file:
            output_file.write("# " + str(e))
