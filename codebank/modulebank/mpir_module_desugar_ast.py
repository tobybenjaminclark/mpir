import argparse
import json
import os


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

def desugar_do_statement(statement):
    statements = []
    identifier = "anon"
    assignment = {
        "TYPE" : "VALUE_ASSIGNMENT",
        "IDENTIFIER" : identifier,
        "EXPRESSION" : statement["EXPRESSION"]
    }

    statements.append(assignment)

    print("DO STATEMENT")
    for index, on_statement in enumerate(statement["ON_STATEMENTS"]):
        print("MATCH TYPE \n\n\n:" + on_statement["MATCH_TYPE"])
        if_statement = {
            "TYPE" : "IF_STATEMENT",
            "EXPRESSION" : {
                "TYPE" : "EXPRESSION_OPERATOR",
                "IDENTIFIER" : "==",
                "LEFT" : {
                    "TYPE" : "EXPRESSION_IDENTIFIER",
                    "IDENTIFIER" : identifier
                },
                "RIGHT" : {
                    "TYPE" : ("EXPRESSION_" + on_statement["MATCH_TYPE"]),
                    ("VALUE" if on_statement["MATCH_TYPE"] == "NUMERICAL_LITERAL" else "IDENTIFIER") : on_statement["MATCH_VALUE"]
                }},
            "MATCH_COMMANDS" : on_statement["MATCH_COMMANDS"]
        }
        print("\tON STATEMENT!")
        statements.append(if_statement)

    return statements



if "CONTENTS" not in ast:
    print("CONTENTS NOT IN AST!")
    exit(1)
else:
    for node in ast["CONTENTS"]:
        if "TYPE" in node and node["TYPE"] == "FUNCTION_DECLARATION":
            for index, statement in enumerate(node["BODY"]):
                if(statement["TYPE"] == "DO_STATEMENT"):
                    new_statements = desugar_do_statement(statement)
                    node["BODY"][index:index + 1] = new_statements
                else:
                    pass
            pass
        elif "TYPE" in node and node["TYPE"] == "TYPE_DECLARATION":
            pass
        else:
            print(node)
            exit(1)

pretty_json = json.dumps(ast, indent=4)
print(pretty_json)