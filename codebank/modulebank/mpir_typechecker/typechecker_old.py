import argparse
import json
import os
import z3
from typing_context import *
from core_calculus import *

def convert_operator_to_z3(operator: str, left, right):
    operator_mapping = {
        # Comparators
        ">": lambda: left > right, ">=": lambda: left >= right, "<": lambda: left < right, "<=": lambda: left <= right, "=": lambda: left == right,
        # Negation, Conjunction & Disjunction
        "∧": lambda:z3.And(left, right), "∨": lambda: z3.Or(left, right), "¬": lambda: z3.Not(left),
        # Predicates (Forall, Exists)
        "∀": lambda: z3.ForAll(left, right), "∃": lambda: z3.Exists(left, right),
    }

    if operator in operator_mapping:
        return operator_mapping[operator]()
    else:
        # Handle the case where the operator is not recognized
        raise ValueError(f"Unsupported operator: {operator}")

# SSA

def form_expression(type_logic: dict):
    match type_logic["DATATYPE"]:
        case "OPERATOR":
            left = form_expression(type_logic["LEFT"])
            right = form_expression(type_logic["RIGHT"])
            return convert_operator_to_z3(type_logic["DATA"], left, right)
        case "IDENTIFIER":
            return z3.Real('x')
        case "STRING_LITERAL":
            pass
        case "NUMERICAL_LITERAL":
            return z3.RealVal(type_logic["DATA"])  # Convert to Z3 Real value

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

from z3 import *

def validate_ast(ast) -> bool:
    return True

def get_operator(operator_str):
    operators = {"+": lambda x, y: x + y,
                 "-": lambda x, y: x - y,
                 "*": lambda x, y: x * y,
                 "/": lambda x, y: x / y}

    return operators.get(operator_str, None)

def type_ast_expression(ast, context) -> bool:
    x = Real('σ')

    match ast["TYPE"]:
        case "EXPRESSION_IDENTIFIER":
            return get_type_from_context(context, ast["IDENTIFIER"])
        case "EXPRESSION_NUMERICAL_LITERAL":
            y = ast["VALUE"]
            return type_create_singular(lambda: x == y)
        case "EXPRESSION_OPERATOR":
            if ast["IDENTIFIER"] == "+":
                l = type_ast_expression(ast["LEFT"], context)
                r = type_ast_expression(ast["RIGHT"], context)
                print(l, "\n\n\n\n", r)
                t3 = T_Add(l, r)
                return t3
        case _:
            print("Error!")

expression_dict = {
        "TYPE": "EXPRESSION_OPERATOR",
        "IDENTIFIER": "+",
        "LEFT": {
            "TYPE": "EXPRESSION_NUMERICAL_LITERAL",
            "VALUE": 5.000000
        },
        "RIGHT": {
            "TYPE": "EXPRESSION_OPERATOR",
            "IDENTIFIER": "+",
            "LEFT": {
                "TYPE": "EXPRESSION_NUMERICAL_LITERAL",
                "VALUE": 1.000000
            },
            "RIGHT" : {
              "TYPE" : "EXPRESSION_NUMERICAL_LITERAL",
              "VALUE" : 1.000000
            }
        }
    }





#ast = parse_json_file("testj.json")
c = context_create()

x = Real('σ')
t = type_create_singular(lambda: z3.And(x > 10, x < 20))
c = c + ('a', t)
type_ast_expression(expression_dict, c)
