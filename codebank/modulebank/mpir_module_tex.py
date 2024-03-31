import argparse
import json
import os

# Function to parse a JSON file (ast, in this case.)
def parse_json_file(filename: str) -> dict|None:
    try: return json.load(open(filename, 'r'))
    except FileNotFoundError as e: print(f"File '{filename}' not found."); return None
    except json.JSONDecodeError as e: print(f"Error decoding AST in '{filename}': {e}"); return None

# Function to convert a function call to pseudocode string.
def convert_function_call(fcall: dict) -> str:
    return fcall["IDENTIFIER"] + "(" + ", ".join([convert_expression(arg["VALUE"]) for arg in fcall["ARGUMENTS"]]) + ")"

# Function to convert an expression to pseudocode string.
def convert_expression(expr: dict) -> str:
    match expr["TYPE"]:
        case "FUNCTION_CALL":                   return convert_function_call(expr)
        case "EXPRESSION_IDENTIFIER":           return expr["IDENTIFIER"]
        case "EXPRESSION_NUMERICAL_LITERAL":    return str(expr["VALUE"])
        case "EXPRESSION_OPERATOR":             return convert_expression(expr["LEFT"]) + " " + expr["IDENTIFIER"] + " " + convert_expression(expr["RIGHT"])
        case "EXPRESSION_STRING_LITERAL":       return expr["IDENTIFIER"]
        case "":                                pass

def build_examples(node, lines):
    if len(list(filter(lambda l: l["FLAG"] == "example", node["DOCSECTION"]))) > 0:
        lines.append("\\textbf{Test Cases}")
        lines.append("\\begin{enumerate}")
        lines.append("\t\\setlength{\\itemsep}{5pt}")
        lines.append("\t\\setlength{\\parskip}{0pt}")
        lines.append("\t\\setlength{\\parsep}{0pt}")
        for line in filter(lambda l: l["FLAG"] == "example", node["DOCSECTION"]):
            lines.append("\t\\item \\verb|" + node["IDENTIFIER"] + line["STRING"].replace("&", "\&") +"|")
        lines.append("\\end{enumerate}\n")
    node["DOCSECTION"] = list(filter(lambda l: l["FLAG"] != "example", node["DOCSECTION"]))

def build_general(node, lines):
    if len(node["DOCSECTION"]) > 0:
        lines.append("\\textbf{Function Information}")
        lines.append("\\begin{itemize}")
        lines.append("\t\\setlength{\\itemsep}{5pt}")
        lines.append("\t\\setlength{\\parskip}{0pt}")
        lines.append("\t\\setlength{\\parsep}{0pt}")
        for index, doc in enumerate(node["DOCSECTION"]):
            if "IDENTIFIER" in doc:
                lines.append("\t\\item \\textbf{" + doc["IDENTIFIER"] + "} \\\\ " + doc["STRING"].replace("&", "\&"))
            else:
                lines.append("\t\\item " + doc["STRING"].replace("&", "\&"))
        lines.append("\\end{itemize}\n")

def build_docsection(node):
    lines = []
    build_examples(node, lines)
    build_general(node, lines)
    return lines

def show_statement(statement):
    if(statement["TYPE"] == "TYPE_ASSIGNMENT"):
        return ("" + statement["ASSIGNED_TYPE"] + " " + statement["IDENTIFIER"] + ";")
    elif(statement["TYPE"] == "VALUE_ASSIGNMENT"):
        return ("" + statement["IDENTIFIER"] + " = " + convert_expression(statement["EXPRESSION"]))
    elif(statement["TYPE"] == "FUNCTION_CALL"):
        return ("" + convert_function_call(statement))
    elif(statement["TYPE"] == "TRYCAST_STATEMENT"):
        return ("TRYCAST!")
    elif(statement["TYPE"] == "DO_STATEMENT"):
        return ("DO STATEMENT!")
    elif(statement["TYPE"] == "IF_STATEMENT"):
        return ("if (", convert_expression(statement["EXPRESSION"]), "): ")
        # for statement2 in statement["MATCH_COMMANDS"]:
        #    show_statement(statement2)

def build_tex(ast):
    lines = []
    lines.append("\n\\section{\\textsc{Function Declarations}}")

    for node in list(filter(lambda x: x["TYPE"] == "FUNCTION_DECLARATION", ast["CONTENTS"])):
        # Start LaTeX Segment
        lines.append("\\clearpage")
        lines.append("\n\\subsection{" + node["IDENTIFIER"].replace("_", "\\_") + "}")
        print("1 ", len(lines))

        lines.extend(build_docsection(node))

        
        # Print Pseudocode
        lines.append("\\begin{minted}[mathescape, linenos, numbersep=5pt, framesep=2mm, frame=lines, fontsize=\\small]{text}")
        output_string = "FUNCTION " + node["IDENTIFIER"] + "("
        for index, arg in enumerate(node["ARGUMENTS"]):
            output_string += arg + ": " + node["INPUTS"][index]
            if index < len(node["ARGUMENTS"]) - 1:
                output_string += ", "
        output_string += ") -> " + node["RETURN_TYPE"] + ":"
        lines.append(output_string)
        print("3 ",len(lines))
        
        for statement in node["BODY"]:
            lines.append("\t" + show_statement(statement))
        lines.append("\\end{minted}\n")
        print("4 ",len(lines))

    lines.append("\n\\section{\\textsc{Type Declarations}}")
    for node in list(filter(lambda x: x["TYPE"] == "TYPE_DECLARATION", ast["CONTENTS"])):
        lines.append("\n\\subsection{" + node["IDENTIFIER"].replace("_", "\\_") + "}")
        docsec = build_docsection(node)
        lines.extend(build_docsection(node))

    return lines

ast = parse_json_file("testj.json")
lines = build_tex(ast)
# Open file for writing
with open('sample.tex', 'w') as file:
    # Write each line to the file
    for l in lines:
        file.write(l + "\n")  # Add a newline character at the end of each line

print(" ")
print(len(lines))
