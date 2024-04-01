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



# Converts AST examples into an enumerated TeX list.
def build_examples(node, lines):
    if len(list(filter(lambda l: l["FLAG"] == "example", node["DOCSECTION"]))) == 0: return

    lines.append("\\textbf{ \\\\ Example Usage of \\texttt{" + node["IDENTIFIER"] + "}}")
    lines.append("\\begin{enumerate}")
    lines.append("\t\\setlength{\\itemsep}{0pt}")
    lines.append("\t\\setlength{\\parskip}{0pt}")
    lines.append("\t\\setlength{\\parsep}{0pt}")
    lines.extend(["\t\\item \\verb|" + node["IDENTIFIER"] + line["STRING"].replace("&", "\&") +"|" for line in filter(lambda l: l["FLAG"] == "example", node["DOCSECTION"])])
    lines.append("\\end{enumerate}\n")
    node["DOCSECTION"] = list(filter(lambda l: l["FLAG"] != "example", node["DOCSECTION"]))



# Converts AST general docs to a bulletpoint list.
def build_general(node, lines):
    if len(node["DOCSECTION"]) == 0: return

    lines.append("\\textbf{ \\\\ Function Information}")
    lines.append("\\begin{itemize}")
    lines.append("\t\\setlength{\\itemsep}{0pt}")
    lines.append("\t\\setlength{\\parskip}{0pt}")
    lines.append("\t\\setlength{\\parsep}{0pt}")
    for index, doc in enumerate(node["DOCSECTION"]):
        if "IDENTIFIER" in doc:
            lines.append("\t\\item \\textbf{" + doc["IDENTIFIER"] + "} \\\\ " + doc["STRING"].replace("&", "\&"))
        else:
            lines.append("\t\\item " + doc["STRING"].replace("&", "\&"))
    lines.append("\\end{itemize}\n")


# Builds web links from docsection
def build_websites(node, lines):
    if len(list(filter(lambda l: l["FLAG"] == "web", node["DOCSECTION"]))) == 0: return

    web_count = 1
    lines.append("\n \\textbf{ \\\\ Useful Links \& Resources}\n")
    for doc in list(filter(lambda l: l["FLAG"] == "web", node["DOCSECTION"])):
        identifier = f"Website {web_count}" if "IDENTIFIER" not in doc else doc["IDENTIFIER"].replace("_", " ")
        lines.append("\\href{" + doc["STRING"] + "}{" + identifier + "} \\hfill \\url{" + doc["STRING"] + "} \n")
    node["DOCSECTION"] = list(filter(lambda l: l["FLAG"] != "web", node["DOCSECTION"]))

def build_description(node, lines):
    if len(list(filter(lambda l: l["FLAG"] == "doc" and "IDENTIFIER" not in l, node["DOCSECTION"]))) == 0: return
    for doc in list(filter(lambda l: l["FLAG"] == "doc" and "IDENTIFIER" not in l, node["DOCSECTION"])):
        lines.append(doc["STRING"] + "\n")
    node["DOCSECTION"] = list(filter(lambda l: False if l["FLAG"] == "doc" and "IDENTIFIER" not in l else True, node["DOCSECTION"]))

    if(len(list(filter(lambda l: l["FLAG"] == "doc" and "IDENTIFIER" in l, node["DOCSECTION"])))) == 0: return
    lines.extend(["\\textbf{ \\\\ Documented Variables in " + node["IDENTIFIER"] + "}", "\\begin{table}[htbp]", "\t\\centering", "\t\\begin{tabular}{|l|l|}", "\t\t\\hline", "\t\tIdentifier & Description 2 \\\\"])
    for doc in list(filter(lambda l: l["FLAG"] == "doc" and "IDENTIFIER" in l, node["DOCSECTION"])):
        lines.extend(["\t\t\\hline", "\t\t \\texttt{" + doc["IDENTIFIER"] + "} & " + doc["STRING"] + " \\\\"])
    lines.extend(["\t\t\\hline", "\t\\end{tabular}", "\\end{table}"])

# Builds docsection
def build_docsection(node):
    lines = []
    build_description(node, lines)
    build_websites(node, lines)
    build_examples(node, lines)
    build_general(node, lines)
    return lines


# Builds pseudocode for trycast
def convert_trycast_statement(statement):
    print(json.dumps(statement, indent = 2))
    lines = []
    lines.append("DOES " + statement["DOMINANT_IDENTIFIER"] + " SATISFY " + statement["CASTED_IDENTIFIER"] + "?")
    lines.append("YES -> " + build_pseudocode_statement(statement["ON_STATEMENTS"][0]["MATCH_COMMANDS"][0])[0])
    lines.append("NO -> " + build_pseudocode_statement(statement["ON_STATEMENTS"][1]["MATCH_COMMANDS"][0])[0])
    return lines


# Builds pseudocode statement
def build_pseudocode_statement(statement):
    match statement["TYPE"]:
        case "TYPE_ASSIGNMENT":     return [f"{statement['ASSIGNED_TYPE']} {statement['IDENTIFIER']};"]
        case "VALUE_ASSIGNMENT":    return [f"{statement['IDENTIFIER']} = {convert_expression(statement['EXPRESSION'])}"]
        case "FUNCTION_CALL":       return [convert_function_call(statement)]
        case "TRYCAST_STATEMENT":   return convert_trycast_statement(statement)
        case "DO_STATEMENT":        return ["DO STATEMENT!"]
        case "IF_STATEMENT":        return [f"if ({convert_expression(statement['EXPRESSION'])}):"]


# Builds function declarationS text
def build_function_declarations(ast, lines):
    lines.append("\n\\section{\\textsc{Function Declarations}}")
    for node in filter(lambda x: x["TYPE"] == "FUNCTION_DECLARATION", ast["CONTENTS"]):
        lines.extend(build_function_declaration(node))

# Builds function declaration tex
def build_function_declaration(node):
    lines = ["\\clearpage"]
    lines.append("\n\\subsection{" + node["IDENTIFIER"].replace("_", "\\_") + "}")
    lines.extend(build_docsection(node))
    lines.extend(build_pseudocode(node))
    return lines

# Builds psuedocode Tex
def build_pseudocode(node):
    pseudocode_lines = ["\\textbf{\\\\ Pseudocode for } \\texttt{" + node["IDENTIFIER"] + "}"]
    pseudocode_lines.append("\\begin{minted}[mathescape, linenos, numbersep=5pt, framesep=2mm, frame=lines, fontsize=\\small]{text}")
    output_string = "FUNCTION " + node["IDENTIFIER"] + "(" + build_arguments(node) + ") -> " + node["RETURN_TYPE"] + ":"
    pseudocode_lines.append(output_string)
    for statement in node["BODY"]:
        pseudocode_lines.extend("\t" + pseudo for pseudo in build_pseudocode_statement(statement))
    pseudocode_lines.append("\\end{minted}\n")
    return pseudocode_lines

# Builds function arguments
def build_arguments(node):
    arguments = []
    for index, arg in enumerate(node["ARGUMENTS"]):
        arguments.append(arg + ": " + node["INPUTS"][index])
    return ", ".join(arguments)


# Build type declarations
def build_type_declarations(ast, lines):
    lines.append("\n\\section{\\textsc{Type Declarations}}")
    for node in list(filter(lambda x: x["TYPE"] == "TYPE_DECLARATION", ast["CONTENTS"])):
        lines.append("\n\\subsection{" + node["IDENTIFIER"].replace("_", "\\_") + "}")
        docsec = build_docsection(node)
        lines.extend(build_docsection(node))



# General Build TeX from ast FUNCTION
def build_tex(ast):
    # lines = ["\\usepackage{minted}", "\\usepackage{hyperref}"]
    lines = []
    build_function_declarations(ast, lines)
    build_type_declarations(ast, lines)
    return lines


def main():
    parser = argparse.ArgumentParser(description='Program to compile MPIR AST File (JSON) to LaTeX.')

    # Add support for version option
    parser.add_argument('-V', '--version', action='version', version='%(prog)s 1.0')
    parser.add_argument('-i', '--input', metavar='input_file', type=str, nargs='?', help='input file path', default='testj.json')
    parser.add_argument('-o', '--output', dest='output_file', metavar='output_file', type=str, help='output file path', default='default_output.tex')
    parser.add_argument('-c', '--config', metavar='config_file', type=str, help='config file path')
    args = parser.parse_args()

    input_file = args.input
    output_file = args.output_file
    config_file = args.config

    # Your code to process input_file and output_file goes here
    print("Input file:", input_file)
    print("Output file:", output_file)

    ast = parse_json_file(input_file)
    lines = build_tex(ast)
    # Open file for writing
    with open(output_file, 'w') as file:
        # Write each line to the file
        for l in lines:
            file.write(l + "\n")  # Add a newline character at the end of each line

    print(" ")
    print(len(lines))

if __name__ == "__main__":
    main()