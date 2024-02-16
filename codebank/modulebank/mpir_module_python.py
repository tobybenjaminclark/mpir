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


args = parse_arguments()
ast = parse_json_file(args.arg1)
print(ast)
# Write the arguments to the specified file
write_arguments_to_file("output.txt", args)
# Access the arguments
print("arg1:", args.arg1)
print("Arguments written to file:", args.output)

if "CONTENTS" not in ast:
    print("CONTENTS NOT IN AST!")
    exit(1)
else:
    for node in ast["CONTENTS"]:
        print(node["TYPE"])
        if "TYPE" in node and node["TYPE"] == "FUNCTION_DECLARATION":
            print("def", node["IDENTIFIER"] + "() ->", node["RETURN_TYPE"] + ":")
            for statement in node["BODY"]:
                if(statement["TYPE"] == "TYPE_ASSIGNMENT"):
                    print("\t" + statement["IDENTIFIER"] + ":", statement["TYPE"])
            pass
        elif "TYPE" in node and node["TYPE"] == "TYPE_DECLARATION":
            pass
        else:
            print(node)
            exit(1)

