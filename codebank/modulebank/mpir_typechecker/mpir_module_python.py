
from z3 import *
from typing_context import *
from typing_context import _context


def convert_expression(expr: dict) -> str:
    """Function to convert an AST expression to a string"""
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
        case "FUNCTION_CALL": return convert_function_call()
    if(expr["TYPE"] == ""):
        pass


def convert_function_call(fcall: dict) -> str:
    """Function to convert a function call to a string. """
    val = fcall["IDENTIFIER"] + "("
    for index, arg in enumerate(fcall["ARGUMENTS"]):
        val = val + convert_expression(arg["VALUE"]) + (", " if index < len(fcall["ARGUMENTS"]) - 1 else "")
    val = val + ")"
    return val


def convert_do_statement(statement: dict, lines: str = "") -> str:
    """Function to convert a do statement to a string."""
    for index, on_statement in enumerate(statement["ON_STATEMENTS"]):
        lines = lines + ("if (" + convert_expression(statement["EXPRESSION"]) + ") ==  " + str(on_statement["MATCH_VALUE"]) + ": ")
        lines = lines + str(on_statement["MATCH_COMMANDS"][0]["IDENTIFIER"]) + " = " + convert_expression(on_statement["MATCH_COMMANDS"][0]["EXPRESSION"]) + "\n\t"
        if index != len(statement["ON_STATEMENTS"]) - 1: lines += "el"
    return lines


def z3_to_string(expr):
    """Function to convert a Z3 Expression to a string."""
    if is_and(expr): return "(" + z3_to_string(expr.children()[0]) + " and " + z3_to_string(expr.children()[1]) + ")"
    elif is_or(expr): return "(" + z3_to_string(expr.children()[0]) + " or " + z3_to_string(expr.children()[1]) + ")"
    elif is_not(expr): return "not " + z3_to_string(expr.children()[0])
    else: return str(expr)
        
    
def convert_trycast_statement(statement: dict, context: _context, lines:str = "") -> str:
    """Function to convert a trycast statement to lines of python code."""
    c_typ = get_type_from_context(context, statement["CASTED_IDENTIFIER"])
    cond = (str(z3_to_string(c_typ.logic.constraint()))).replace("σ", statement["DOMINANT_IDENTIFIER"])
    for index, on_statement in enumerate(statement["ON_STATEMENTS"]):
        lines += "if(" + cond + ") == " + ("True" if on_statement["MATCH_VALUE"] == 1 else "False") + ": " + on_statement["MATCH_COMMANDS"][0]["IDENTIFIER"] + " = " + convert_expression(on_statement["MATCH_COMMANDS"][0]["EXPRESSION"]) + "\n\t"
        if index != len(statement["ON_STATEMENTS"]) - 1: lines += "el"
    return lines


def show_statement(statement, output_file, context):
    """Function to convert a imperative statement to a python string."""
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
        

def build_python(ast: dict[str, any], output_file_path: str, context: _context):
    """Function to generate Python code from AST and writes to a python file."""
    output_file = open(output_file_path, 'w')

    # Try and write the AST to the file.
    try:
        if "CONTENTS" not in ast: raise Exception("Something's gone wrong, Invalid AST!")
        output_file.write("# Generated using the MPIR Compiler.\n\n")
        build_types(ast, output_file, context)
        build_functions(ast, output_file, context)

    # Write Exceptions as comments. (If one happens!)
    except Exception as e:  output_file.write("# " + str(e))
    finally:                output_file.close()


def build_types(ast: dict[str, any], output_file, context) -> None:
    """Function to write  type declarations to the python file."""
    for node in filter(lambda v: v["TYPE"] == "TYPE_DECLARATION", ast["CONTENTS"]):
        identifier, representation = node["IDENTIFIER"], "σ | " + z3_to_string(get_type_from_context(context, node["IDENTIFIER"]).logic.constraint())
        output_file.write(f"# Type Declaration of {identifier} :: {representation} (Statically Verified) \n{identifier} = type('{identifier}', (), {{}})\n\n")
    output_file.write("Numerical = type('Numerical', (float, ), {})\n\n")
    return None


def build_functions(ast: dict[str, any], output_file, context: _context) -> None:
    """Function to write function declarations to the python file."""
    for node in filter(lambda v: v["TYPE"] == "FUNCTION_DECLARATION", ast["CONTENTS"]):
        output_file.write("def " + node["IDENTIFIER"] + "(")
        write_function_arguments(node, output_file)
        output_file.write(") -> " + node["RETURN_TYPE"] + ":\n")
        write_function_body(node, output_file, context)
        output_file.write("\n\n")
    return None


def write_function_arguments(node: dict, output_file) -> None:
    """Function to write  function arguments to the python file."""
    for index, arg in enumerate(node["ARGUMENTS"]):
        output_file.write(arg + ": " + node["INPUTS"][index]["TYPE"] + (", " if index < len(node["ARGUMENTS"]) - 1 else ""))
    return None


def write_function_body(node: dict, output_file, context) -> None:
    """Function to write  function body statements to the python file."""
    for statement in node["BODY"]:
        output_file.write("\t")
        show_statement(statement, output_file, context)
    return None