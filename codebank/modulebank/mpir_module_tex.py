import argparse
import json

import os

# get the current working directory
current_working_directory = os.getcwd()

# print output to the console
print(current_working_directory)

def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description='Build MPiR AST to Python3 Code')
    parser.add_argument('arg1', type=str, help='Input File')
    parser.add_argument('--output', type=str, help='Output File', default = "output.py")
    return parser.parse_args()

def write_arguments_to_file(filename: str, args: argparse.Namespace):
    with open(filename, 'w') as file:
        file.write("arg1: {}\n".format(args.arg1))

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


ast = parse_json_file("testj.json")

def convert_function_call(fcall: dict) -> str:
    val = fcall["IDENTIFIER"] + "("
    for index, arg in enumerate(fcall["ARGUMENTS"]):
        val = val + convert_expression(arg["VALUE"]) + (", " if index < len(fcall["ARGUMENTS"]) - 1 else "")
    val = val + ")"
    return val

def convert_expression(expr: dict) -> str:
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
    if(expr["TYPE"] == ""):
        pass

def show_statement(statement):
    if(statement["TYPE"] == "TYPE_ASSIGNMENT"):
        print("" + statement["ASSIGNED_TYPE"] + " " + statement["IDENTIFIER"] + ";")
    elif(statement["TYPE"] == "VALUE_ASSIGNMENT"):
        print("" + statement["IDENTIFIER"], "=", convert_expression(statement["EXPRESSION"]))
    elif(statement["TYPE"] == "FUNCTION_CALL"):
        print("" + convert_function_call(statement))
    elif(statement["TYPE"] == "TRYCAST_STATEMENT"):
        print("TRYCAST!")
    elif(statement["TYPE"] == "DO_STATEMENT"):
        print("DO STATEMENT!")
    elif(statement["TYPE"] == "IF_STATEMENT"):
        print("if (", convert_expression(statement["EXPRESSION"]), "): ", end = "")
        for statement2 in statement["MATCH_COMMANDS"]:
            show_statement(statement2)

if "CONTENTS" not in ast:
    print("CONTENTS NOT IN AST!")
    exit(1)


print("\n\\section{\\textsc{Function Declarations}}")
for node in list(filter(lambda x: x["TYPE"] == "FUNCTION_DECLARATION", ast["CONTENTS"])):
    # Start LaTeX Segment
    print("\n\\subsection{" + node["IDENTIFIER"].replace("_", "\\_") + "}")

    # Print Docs
    if len(node["DOCSECTION"]) > 0:
        print("\\begin{itemize}")
        print("\t\\setlength{\\itemsep}{5pt}")
        print("\t\\setlength{\\parskip}{0pt}")
        print("\t\\setlength{\\parsep}{0pt}")
    
        for index, doc in enumerate(node["DOCSECTION"]):
            if "IDENTIFIER" in doc:
                print("\t\\item \\textbf{" + doc["IDENTIFIER"] + "} \\\\ " + doc["STRING"].replace("&", "\&"))
            else:
                print("\t\\item " + doc["STRING"].replace("&", "\&"))
        print("\\end{itemize}\n")


    # Print Pseudocode
    print("\\begin{minted}[mathescape, linenos, numbersep=5pt, framesep=2mm, frame=lines, fontsize=\\small]{text}")
    print("FUNCTION ", node["IDENTIFIER"] + "(", end="")
    for index, arg in enumerate(node["ARGUMENTS"]):
        print(arg + ":", node["INPUTS"][index], end=", " if index < len(node["ARGUMENTS"]) - 1 else "")
    print(") ->", node["RETURN_TYPE"] + ":")
    for statement in node["BODY"]:
        print("    ", end = "")
        show_statement(statement)
    print("\\end{minted}\n")

print("\n\\section{\\textsc{Type Declarations}}")
for node in list(filter(lambda x: x["TYPE"] == "FUNCTION_DECLARATION", ast["CONTENTS"])):
    print(node["IDENTIFIER"])
    

